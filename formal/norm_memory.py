"""
Memory lowering on normalized IR.

This pass resolves straight-line memory stores/loads into explicit
value flow before restricted lowering.

Supported:
- straight-line ``mstore`` / ``NStore``
- ``mload`` reads from previously written constant addresses
- read-only control-flow bodies (``if`` / ``switch``) that may perform
  ``mload`` from the current straight-line memory state
- constant-address aliases tracked through normalized bind/assigns

Rejected:
- non-constant or unaligned addresses
- duplicate writes / overwrites
- reads before writes
- memory writes inside control flow
"""

from __future__ import annotations

from norm_constprop import fold_expr
from norm_ir import (
    NAssign,
    NBind,
    NBlock,
    NBuiltinCall,
    NConst,
    NExpr,
    NExprEffect,
    NFor,
    NFunctionDef,
    NIf,
    NLeave,
    NormalizedFunction,
    NRef,
    NStmt,
    NStore,
    NSwitch,
    NSwitchCase,
)
from norm_walk import for_each_expr, map_expr, max_symbol_id
from yul_ast import ParseError, SymbolId


def _subst_consts(expr: NExpr, env: dict[SymbolId, NConst]) -> NExpr:
    def rewrite(e: NExpr) -> NExpr:
        if isinstance(e, NRef):
            return env.get(e.symbol_id, e)
        return e

    return map_expr(expr, rewrite)


def _resolve_const_addr(
    expr: NExpr,
    op: str,
    env: dict[SymbolId, NConst],
) -> int:
    folded = fold_expr(_subst_consts(expr, env))
    if not isinstance(folded, NConst):
        raise ParseError(
            f"Non-constant {op} address: {expr!r}. "
            f"The memory model requires constant 32-byte-aligned addresses."
        )
    addr = folded.value
    if addr % 32 != 0:
        raise ParseError(f"Unaligned {op} address {addr} (must be 32-byte aligned)")
    return addr


def _expr_has_memory_write(expr: NExpr) -> bool:
    found = False

    def check(e: NExpr) -> None:
        nonlocal found
        if isinstance(e, NBuiltinCall) and e.op in ("mstore", "mstore8"):
            found = True

    for_each_expr(expr, check)
    return found


def _reject_memory_writes_in_block(block: NBlock, context: str) -> None:
    for stmt in block.stmts:
        _reject_memory_writes_in_stmt(stmt, context)


def _reject_memory_writes_in_stmt(stmt: NStmt, context: str) -> None:
    if isinstance(stmt, NStore):
        raise ParseError(
            f"Memory write inside control flow ({context}). "
            f"The memory model requires straight-line memory writes."
        )
    if isinstance(stmt, NExprEffect):
        if _expr_has_memory_write(stmt.expr):
            raise ParseError(
                f"Memory write inside control flow ({context}). "
                f"The memory model requires straight-line memory writes."
            )
        return
    if isinstance(stmt, (NBind, NAssign)):
        if stmt.expr is not None and _expr_has_memory_write(stmt.expr):
            raise ParseError(
                f"Memory write inside control flow ({context}). "
                f"The memory model requires straight-line memory writes."
            )
        return
    if isinstance(stmt, NIf):
        if _expr_has_memory_write(stmt.condition):
            raise ParseError(
                f"Memory write inside control flow ({context}). "
                f"The memory model requires straight-line memory writes."
            )
        _reject_memory_writes_in_block(stmt.then_body, context)
        return
    if isinstance(stmt, NSwitch):
        if _expr_has_memory_write(stmt.discriminant):
            raise ParseError(
                f"Memory write inside control flow ({context}). "
                f"The memory model requires straight-line memory writes."
            )
        for case in stmt.cases:
            _reject_memory_writes_in_block(case.body, context)
        if stmt.default is not None:
            _reject_memory_writes_in_block(stmt.default, context)
        return
    if isinstance(stmt, NFor):
        if _expr_has_memory_write(stmt.condition):
            raise ParseError(
                f"Memory write inside control flow ({context}). "
                f"The memory model requires straight-line memory writes."
            )
        _reject_memory_writes_in_block(stmt.init, context)
        if stmt.condition_setup is not None:
            _reject_memory_writes_in_block(stmt.condition_setup, context)
        _reject_memory_writes_in_block(stmt.post, context)
        _reject_memory_writes_in_block(stmt.body, context)
        return
    if isinstance(stmt, NBlock):
        _reject_memory_writes_in_block(stmt, context)


def _resolve_memory_in_expr(
    expr: NExpr,
    mem: dict[int, NExpr],
    env: dict[SymbolId, NConst],
) -> NExpr:
    def rewrite(e: NExpr) -> NExpr:
        if isinstance(e, NRef):
            return env.get(e.symbol_id, e)
        if isinstance(e, NBuiltinCall) and e.op == "mload" and len(e.args) == 1:
            addr = _resolve_const_addr(e.args[0], "mload", env)
            if addr not in mem:
                available = sorted(mem.keys())
                raise ParseError(
                    f"mload from address {addr} which has no prior mstore. "
                    f"Available addresses: {available}"
                )
            return mem[addr]
        return e

    return fold_expr(map_expr(expr, rewrite))


class _MemCtx:
    def __init__(self, next_id: int) -> None:
        self.mem: dict[int, NExpr] = {}
        self._next_id = next_id

    def alloc(self) -> SymbolId:
        sid = SymbolId(self._next_id)
        self._next_id += 1
        return sid


def _update_const_env(
    targets: tuple[SymbolId, ...],
    expr: NExpr | None,
    env: dict[SymbolId, NConst],
) -> None:
    if expr is not None and len(targets) == 1 and isinstance(expr, NConst):
        env[targets[0]] = expr
        return
    for sid in targets:
        env.pop(sid, None)


def _join_const_envs(envs: list[dict[SymbolId, NConst]]) -> dict[SymbolId, NConst]:
    if not envs:
        return {}
    common = set(envs[0].keys())
    for env in envs[1:]:
        common &= set(env.keys())
    joined: dict[SymbolId, NConst] = {}
    for sid in common:
        value = envs[0][sid]
        if all(env[sid] == value for env in envs[1:]):
            joined[sid] = value
    return joined


def _emit_store(
    *,
    addr: int,
    value_expr: NExpr,
    ctx: _MemCtx,
    env: dict[SymbolId, NConst],
    out: list[NStmt],
) -> None:
    if addr in ctx.mem:
        raise ParseError(
            f"Duplicate mstore to address {addr}. "
            f"The memory model forbids aliasing or overwriting."
        )
    resolved_value = _resolve_memory_in_expr(value_expr, ctx.mem, env)
    if isinstance(resolved_value, NConst):
        ctx.mem[addr] = resolved_value
        return
    tid = ctx.alloc()
    name = f"_mem_{addr}"
    out.append(NBind(targets=(tid,), target_names=(name,), expr=resolved_value))
    ctx.mem[addr] = NRef(symbol_id=tid, name=name)


def _lower_block(
    block: NBlock,
    ctx: _MemCtx,
    env: dict[SymbolId, NConst],
) -> NBlock:
    out: list[NStmt] = []
    for stmt in block.stmts:
        _lower_stmt(stmt, ctx, env, out)
    return NBlock(tuple(out))


def _lower_stmt(
    stmt: NStmt,
    ctx: _MemCtx,
    env: dict[SymbolId, NConst],
    out: list[NStmt],
) -> None:
    if isinstance(stmt, NStore):
        addr = _resolve_const_addr(stmt.addr, "mstore", env)
        _emit_store(addr=addr, value_expr=stmt.value, ctx=ctx, env=env, out=out)
        return

    if isinstance(stmt, NBind):
        if stmt.expr is None:
            for sid in stmt.targets:
                env[sid] = NConst(0)
            out.append(stmt)
            return
        new_expr = _resolve_memory_in_expr(stmt.expr, ctx.mem, env)
        _update_const_env(stmt.targets, new_expr, env)
        out.append(
            NBind(targets=stmt.targets, target_names=stmt.target_names, expr=new_expr)
        )
        return

    if isinstance(stmt, NAssign):
        new_expr = _resolve_memory_in_expr(stmt.expr, ctx.mem, env)
        _update_const_env(stmt.targets, new_expr, env)
        out.append(
            NAssign(targets=stmt.targets, target_names=stmt.target_names, expr=new_expr)
        )
        return

    if isinstance(stmt, NExprEffect):
        if (
            isinstance(stmt.expr, NBuiltinCall)
            and stmt.expr.op == "mstore"
            and len(stmt.expr.args) == 2
        ):
            addr = _resolve_const_addr(stmt.expr.args[0], "mstore", env)
            _emit_store(
                addr=addr, value_expr=stmt.expr.args[1], ctx=ctx, env=env, out=out
            )
            return
        out.append(NExprEffect(expr=_resolve_memory_in_expr(stmt.expr, ctx.mem, env)))
        return

    if isinstance(stmt, NIf):
        _reject_memory_writes_in_block(stmt.then_body, "if-body")
        before_env = dict(env)
        then_env = dict(env)
        new_cond = _resolve_memory_in_expr(stmt.condition, ctx.mem, env)
        then_body = _lower_block(stmt.then_body, ctx, then_env)
        env.clear()
        env.update(_join_const_envs([before_env, then_env]))
        out.append(NIf(condition=new_cond, then_body=then_body))
        return

    if isinstance(stmt, NSwitch):
        for case in stmt.cases:
            _reject_memory_writes_in_block(case.body, "switch-case")
        if stmt.default is not None:
            _reject_memory_writes_in_block(stmt.default, "switch-default")
        new_disc = _resolve_memory_in_expr(stmt.discriminant, ctx.mem, env)
        branch_envs: list[dict[SymbolId, NConst]] = []
        new_cases: list[NSwitchCase] = []
        for case in stmt.cases:
            case_env = dict(env)
            branch_envs.append(case_env)
            new_cases.append(
                NSwitchCase(
                    value=case.value, body=_lower_block(case.body, ctx, case_env)
                )
            )
        new_default = None
        if stmt.default is not None:
            default_env = dict(env)
            branch_envs.append(default_env)
            new_default = _lower_block(stmt.default, ctx, default_env)
        else:
            branch_envs.append(dict(env))
        env.clear()
        env.update(_join_const_envs(branch_envs))
        out.append(
            NSwitch(discriminant=new_disc, cases=tuple(new_cases), default=new_default)
        )
        return

    if isinstance(stmt, NFor):
        _reject_memory_writes_in_block(stmt.init, "for-init")
        if stmt.condition_setup is not None:
            _reject_memory_writes_in_block(stmt.condition_setup, "for-condition-setup")
        _reject_memory_writes_in_block(stmt.post, "for-post")
        _reject_memory_writes_in_block(stmt.body, "for-body")
        new_cond = _resolve_memory_in_expr(stmt.condition, ctx.mem, env)
        new_cond_setup = (
            _lower_block(stmt.condition_setup, ctx, dict(env))
            if stmt.condition_setup is not None
            else None
        )
        out.append(
            NFor(
                init=stmt.init,
                condition=new_cond,
                condition_setup=new_cond_setup,
                post=stmt.post,
                body=stmt.body,
            )
        )
        return

    if isinstance(stmt, (NLeave, NFunctionDef)):
        out.append(stmt)
        return

    if isinstance(stmt, NBlock):
        out.append(_lower_block(stmt, ctx, env))
        return

    raise ParseError(f"Unexpected statement in memory lowering: {type(stmt).__name__}")


def lower_memory(func: NormalizedFunction) -> NormalizedFunction:
    """Resolve normalized-IR memory operations into direct value flow."""
    ctx = _MemCtx(next_id=max_symbol_id(func) + 1)
    new_body = _lower_block(func.body, ctx, {})
    return NormalizedFunction(
        name=func.name,
        params=func.params,
        param_names=func.param_names,
        returns=func.returns,
        return_names=func.return_names,
        body=new_body,
    )
