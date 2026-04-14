"""Memory lowering on normalized IR.

This pass resolves straight-line memory stores/loads into explicit
value flow before restricted lowering. It is intentionally narrow:
it resolves memory semantics and lets the ordinary normalized-IR
simplifier clean up any newly dead control flow afterward.

Supported:
- straight-line ``mstore``
- ``mload`` reads in straight-line code and control-flow conditions
- free-pointer-relative addresses of the form ``free + k`` where
  ``0 <= k < 2^64`` and ``k`` is 32-byte aligned
- last-write-wins semantics for modeled slots

Rejected:
- memory writes inside dynamic control flow
- ``mstore8``
- unaligned addresses
- reads before writes from modeled word slots
- writes or reads to forbidden constant slots
- negative, non-constant, or oversized free-relative offsets
- free-pointer values escaping ordinary value flow
- for-loops
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import assert_never

from .norm_constprop import fold_expr
from .norm_ir import (
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
    NIte,
    NLeave,
    NLocalCall,
    NormalizedFunction,
    NRef,
    NStmt,
    NSwitch,
    NSwitchCase,
    NTopLevelCall,
    NUnresolvedCall,
)
from .norm_walk import (
    NBlockItem,
    collect_function_defs,
    const_truthy,
    const_value,
    expr_contains,
    first_runtime_local_call,
    for_each_stmt,
    for_each_stmt_expr,
    map_expr,
    max_symbol_id,
)
from .yul_ast import LoweringError, SymbolId

_MODELED_CONST_SLOTS = frozenset({0, 32, 64, 96})
_WRITABLE_WORD_SLOTS = frozenset({0, 32})
_FREE_PTR_SLOT = 64
_READONLY_ZERO_SLOT = 96
_MAX_FREE_PTR_OFFSET = 1 << 64


@dataclass(frozen=True)
class _FreePtr:
    offset: int

    def __post_init__(self) -> None:
        if self.offset < 0:
            raise ValueError("free-pointer offsets must be non-negative")
        if self.offset >= _MAX_FREE_PTR_OFFSET:
            raise ValueError("free-pointer offsets must be below 2^64")
        if self.offset % 32 != 0:
            raise ValueError("free-pointer offsets must be 32-byte aligned")


@dataclass(frozen=True)
class _ConstSlot:
    addr: int


@dataclass(frozen=True)
class _FreeSlot:
    offset: int


_MemAddr = _ConstSlot | _FreeSlot
_Fact = NConst | _FreePtr
_MemValue = NExpr | _FreePtr


class _FactEnv:
    def __init__(self) -> None:
        self.known: dict[SymbolId, _Fact] = {}
        self.pointer_taint: set[SymbolId] = set()

    def copy(self) -> _FactEnv:
        other = _FactEnv()
        other.known = dict(self.known)
        other.pointer_taint = set(self.pointer_taint)
        return other

    def update_from(self, other: _FactEnv) -> None:
        """Replace this environment's state with *other*'s state."""
        self.known = dict(other.known)
        self.pointer_taint = set(other.pointer_taint)

    def fact(self, sid: SymbolId) -> _Fact | None:
        return self.known.get(sid)

    def is_tainted(self, sid: SymbolId) -> bool:
        return sid in self.pointer_taint

    def set_const(self, sid: SymbolId, value: NConst) -> None:
        self.known[sid] = value
        self.pointer_taint.discard(sid)

    def set_unknown_word(self, sid: SymbolId) -> None:
        self.known.pop(sid, None)
        self.pointer_taint.discard(sid)

    def set_pointer(self, sid: SymbolId, ptr: _FreePtr) -> None:
        self.known[sid] = ptr
        self.pointer_taint.add(sid)


class _MemoryState:
    def __init__(self) -> None:
        self.const_words: dict[int, NExpr] = {_READONLY_ZERO_SLOT: NConst(0)}
        self.free_ptr = _FreePtr(0)
        self.free_words: dict[int, NExpr] = {}

    def load(self, addr: _MemAddr, *, op: str) -> _MemValue:
        if isinstance(addr, _ConstSlot):
            if addr.addr == _FREE_PTR_SLOT:
                return self.free_ptr
            if addr.addr in self.const_words:
                return self.const_words[addr.addr]
            raise LoweringError(
                f"{op} from slot {addr.addr} before write. "
                "The memory model forbids reads before writes."
            )
        if addr.offset not in self.free_words:
            raise LoweringError(
                f"{op} from free-relative slot {addr.offset} before write. "
                "The memory model forbids reads before writes."
            )
        return self.free_words[addr.offset]

    def store(self, addr: _MemAddr, value: _MemValue, *, op: str) -> None:
        if isinstance(addr, _ConstSlot):
            if addr.addr in _WRITABLE_WORD_SLOTS:
                if isinstance(value, _FreePtr):
                    raise LoweringError(
                        f"{op} to slot {addr.addr} cannot store the free pointer. "
                        "Only slot 64 may hold free-relative addresses."
                    )
                self.const_words[addr.addr] = value
                return
            if addr.addr == _FREE_PTR_SLOT:
                if not isinstance(value, _FreePtr):
                    raise LoweringError(
                        f"{op} to slot 64 must store a free-relative pointer."
                    )
                self.free_ptr = value
                return
            if addr.addr == _READONLY_ZERO_SLOT:
                raise LoweringError("Writes to slot 96 are forbidden.")
            raise LoweringError(f"{op} to unsupported constant slot {addr.addr}.")

        if isinstance(value, _FreePtr):
            raise LoweringError(
                f"{op} to free-relative slot {addr.offset} cannot store the free pointer."
            )
        self.free_words[addr.offset] = value


def _subst_consts(expr: NExpr, env: dict[SymbolId, NConst]) -> NExpr:
    def rewrite(e: NExpr) -> NExpr:
        if isinstance(e, NRef):
            return env.get(e.symbol_id, e)
        return e

    return map_expr(expr, rewrite)


def _subst_const_facts(expr: NExpr, env: _FactEnv) -> NExpr:
    const_env: dict[SymbolId, NConst] = {}
    for sid, fact in env.known.items():
        if isinstance(fact, NConst):
            const_env[sid] = fact
    return _subst_consts(expr, const_env)


def _resolve_const_value(expr: NExpr, env: _FactEnv) -> int | None:
    folded = fold_expr(_subst_const_facts(expr, env))
    return const_value(folded)


def _resolve_offset_value(expr: NExpr, env: _FactEnv) -> int | None:
    rewritten = _subst_const_facts(expr, env)
    if isinstance(rewritten, NConst):
        return rewritten.value
    if isinstance(rewritten, NBuiltinCall) and len(rewritten.args) == 2:
        lhs = _resolve_offset_value(rewritten.args[0], env)
        rhs = _resolve_offset_value(rewritten.args[1], env)
        if lhs is not None and rhs is not None:
            if rewritten.op == "add":
                return lhs + rhs
            if rewritten.op == "sub":
                return lhs - rhs
    folded = fold_expr(rewritten)
    if isinstance(folded, NConst):
        return folded.value
    return None


def _require_aligned_addr(addr: int, op: str) -> None:
    if addr % 32 != 0:
        raise LoweringError(f"Unaligned {op} address {addr} (must be 32-byte aligned)")


def _require_free_offset(offset: int, op: str) -> None:
    if offset < 0:
        raise LoweringError(f"{op} with negative free-relative offset is forbidden.")
    if offset >= _MAX_FREE_PTR_OFFSET:
        raise LoweringError(f"{op} with free-relative offset >= 2^64 is forbidden.")
    _require_aligned_addr(offset, op)


def _resolve_const_slot(
    expr: NExpr,
    op: str,
    env: _FactEnv,
) -> _ConstSlot | None:
    addr = _resolve_const_value(expr, env)
    if addr is None:
        return None
    _require_aligned_addr(addr, op)
    if addr not in _MODELED_CONST_SLOTS:
        raise LoweringError(
            f"{op} at forbidden constant address {addr}. "
            "Only slots 0, 32, 64, and 96 are modeled."
        )
    return _ConstSlot(addr)


def _offset_free_ptr(ptr: _FreePtr, delta: int, op: str) -> _FreePtr:
    new_offset = ptr.offset + delta
    _require_free_offset(new_offset, op)
    return _FreePtr(new_offset)


def _resolve_pointer_expr(
    expr: NExpr,
    mem: _MemoryState,
    env: _FactEnv,
) -> _FreePtr | None:
    if isinstance(expr, NRef):
        fact = env.fact(expr.symbol_id)
        if isinstance(fact, _FreePtr):
            return fact
        if env.is_tainted(expr.symbol_id):
            raise LoweringError(
                f"Pointer value {expr.name!r} is not uniquely known after control flow."
            )
        return None

    if isinstance(expr, NBuiltinCall):
        if expr.op == "mload" and len(expr.args) == 1:
            value = mem.load(
                _resolve_addr(expr.args[0], "mload", mem, env),
                op="mload",
            )
            if isinstance(value, _FreePtr):
                return value
            return None

        if expr.op in ("add", "sub") and len(expr.args) == 2:
            lhs_ptr = _resolve_pointer_expr(expr.args[0], mem, env)
            rhs_ptr = _resolve_pointer_expr(expr.args[1], mem, env)

            if lhs_ptr is None and rhs_ptr is None:
                return None
            if lhs_ptr is not None and rhs_ptr is not None:
                raise LoweringError(
                    "Free-relative addresses may use at most one free-pointer base."
                )
            if lhs_ptr is not None:
                delta = _resolve_offset_value(expr.args[1], env)
                if delta is None:
                    raise LoweringError(
                        "Free-relative addresses require a constant offset."
                    )
                if expr.op == "sub":
                    delta = -delta
                return _offset_free_ptr(lhs_ptr, delta, expr.op)

            assert rhs_ptr is not None
            if expr.op == "sub":
                raise LoweringError(
                    "Free-relative addresses cannot subtract a free-pointer base."
                )
            delta = _resolve_offset_value(expr.args[0], env)
            if delta is None:
                raise LoweringError(
                    "Free-relative addresses require a constant offset."
                )
            return _offset_free_ptr(rhs_ptr, delta, expr.op)

    if isinstance(expr, NIte):
        true_ptr = _resolve_pointer_expr(expr.if_true, mem, env)
        false_ptr = _resolve_pointer_expr(expr.if_false, mem, env)
        if true_ptr is None and false_ptr is None:
            return None
        if true_ptr == false_ptr and true_ptr is not None:
            return true_ptr
        raise LoweringError("Conditional free-pointer values are forbidden.")

    return None


def _resolve_addr(
    expr: NExpr,
    op: str,
    mem: _MemoryState,
    env: _FactEnv,
) -> _MemAddr:
    const_slot = _resolve_const_slot(expr, op, env)
    if const_slot is not None:
        return const_slot
    ptr = _resolve_pointer_expr(expr, mem, env)
    if ptr is None:
        raise LoweringError(
            f"Non-constant {op} address: {expr!r}. "
            "Addresses must be one of the modeled constant slots or free + const."
        )
    return _FreeSlot(ptr.offset)


def _expr_has_memory_write(expr: NExpr) -> bool:
    return expr_contains(
        expr,
        lambda e: isinstance(e, NBuiltinCall) and e.op in ("mstore", "mstore8"),
    )


def _reject_memory_writes_in_block(block: NBlock, context: str) -> None:
    def reject(item: NBlockItem) -> None:
        if isinstance(item, NFunctionDef):
            return
        for_each_stmt_expr(
            item,
            lambda expr: _reject_expr_memory_write(expr, context),
        )

    for_each_stmt(block, reject)


def _reject_expr_memory_write(expr: NExpr, context: str) -> None:
    if _expr_has_memory_write(expr):
        raise LoweringError(
            f"Memory write inside control flow ({context}). "
            f"The memory model requires straight-line memory writes."
        )


def _resolve_word_expr(
    expr: NExpr,
    mem: _MemoryState,
    env: _FactEnv,
) -> NExpr:
    if isinstance(expr, NConst):
        return expr
    if isinstance(expr, NRef):
        fact = env.fact(expr.symbol_id)
        if isinstance(fact, NConst):
            return fact
        if env.is_tainted(expr.symbol_id):
            raise LoweringError(
                f"free-pointer value {expr.name!r} escapes ordinary value flow."
            )
        return expr
    if isinstance(expr, NBuiltinCall):
        if expr.op == "mload" and len(expr.args) == 1:
            value = mem.load(_resolve_addr(expr.args[0], "mload", mem, env), op="mload")
            if isinstance(value, _FreePtr):
                raise LoweringError(
                    "free-pointer value escapes ordinary value flow via mload."
                )
            return value
        if expr.op == "mstore8":
            raise LoweringError("mstore8 is forbidden by the memory model.")
        return fold_expr(
            NBuiltinCall(
                op=expr.op,
                args=tuple(_resolve_word_expr(arg, mem, env) for arg in expr.args),
            )
        )
    if isinstance(expr, NLocalCall):
        return NLocalCall(
            symbol_id=expr.symbol_id,
            name=expr.name,
            args=tuple(_resolve_word_expr(arg, mem, env) for arg in expr.args),
        )
    if isinstance(expr, NTopLevelCall):
        return NTopLevelCall(
            name=expr.name,
            args=tuple(_resolve_word_expr(arg, mem, env) for arg in expr.args),
        )
    if isinstance(expr, NUnresolvedCall):
        return NUnresolvedCall(
            name=expr.name,
            args=tuple(_resolve_word_expr(arg, mem, env) for arg in expr.args),
        )
    if isinstance(expr, NIte):
        return fold_expr(
            NIte(
                cond=_resolve_word_expr(expr.cond, mem, env),
                if_true=_resolve_word_expr(expr.if_true, mem, env),
                if_false=_resolve_word_expr(expr.if_false, mem, env),
            )
        )
    assert_never(expr)


class _MemCtx:
    def __init__(self, next_id: int) -> None:
        self.mem = _MemoryState()
        self._next_id = next_id

    def alloc(self) -> SymbolId:
        sid = SymbolId(self._next_id)
        self._next_id += 1
        return sid


def _update_fact_env(
    targets: tuple[SymbolId, ...],
    value: _MemValue | None,
    env: _FactEnv,
) -> None:
    if len(targets) != 1 or value is None:
        for sid in targets:
            env.set_unknown_word(sid)
        return
    target = targets[0]
    if isinstance(value, NConst):
        env.set_const(target, value)
        return
    if isinstance(value, _FreePtr):
        env.set_pointer(target, value)
        return
    env.set_unknown_word(target)


def _join_fact_envs(envs: list[_FactEnv]) -> _FactEnv:
    joined = _FactEnv()
    if not envs:
        return joined
    all_sids: set[SymbolId] = set()
    for env in envs:
        all_sids.update(env.known)
        all_sids.update(env.pointer_taint)
    for sid in all_sids:
        facts = [env.fact(sid) for env in envs]
        first = facts[0]
        if first is not None and all(fact == first for fact in facts[1:]):
            joined.known[sid] = first
        if any(env.is_tainted(sid) for env in envs):
            joined.pointer_taint.add(sid)
    return joined


def _resolve_binding_value(
    expr: NExpr,
    mem: _MemoryState,
    env: _FactEnv,
) -> _MemValue:
    ptr = _resolve_pointer_expr(expr, mem, env)
    if ptr is not None:
        return ptr
    return _resolve_word_expr(expr, mem, env)


def _snapshot_word(value: NExpr, ctx: _MemCtx, out: list[NStmt], name: str) -> NExpr:
    if isinstance(value, NConst):
        return value
    tid = ctx.alloc()
    out.append(NBind(targets=(tid,), target_names=(name,), expr=value))
    return NRef(symbol_id=tid, name=name)


def _emit_store(
    *,
    addr: _MemAddr,
    value_expr: NExpr,
    ctx: _MemCtx,
    env: _FactEnv,
    out: list[NStmt],
) -> None:
    resolved_value = _resolve_binding_value(value_expr, ctx.mem, env)
    if isinstance(resolved_value, _FreePtr):
        ctx.mem.store(addr, resolved_value, op="mstore")
        return
    name = (
        f"_mem_{addr.addr}"
        if isinstance(addr, _ConstSlot)
        else f"_mem_free_{addr.offset}"
    )
    ctx.mem.store(addr, _snapshot_word(resolved_value, ctx, out, name), op="mstore")


def _lower_block(
    block: NBlock,
    ctx: _MemCtx,
    env: _FactEnv,
) -> NBlock:
    out: list[NStmt] = []
    for stmt in block.stmts:
        _lower_stmt(stmt, ctx, env, out)
    return NBlock(defs=block.defs, stmts=tuple(out))


def _lower_stmt(
    stmt: NStmt,
    ctx: _MemCtx,
    env: _FactEnv,
    out: list[NStmt],
) -> None:
    if isinstance(stmt, NBind):
        if stmt.expr is None:
            for sid in stmt.targets:
                env.set_const(sid, NConst(0))
            out.append(stmt)
            return
        value = _resolve_binding_value(stmt.expr, ctx.mem, env)
        _update_fact_env(stmt.targets, value, env)
        if isinstance(value, _FreePtr):
            if len(stmt.targets) != 1:
                raise LoweringError(
                    "Pointer-valued bindings must have exactly one target."
                )
            return
        out.append(
            NBind(targets=stmt.targets, target_names=stmt.target_names, expr=value)
        )
        return

    if isinstance(stmt, NAssign):
        value = _resolve_binding_value(stmt.expr, ctx.mem, env)
        _update_fact_env(stmt.targets, value, env)
        if isinstance(value, _FreePtr):
            if len(stmt.targets) != 1:
                raise LoweringError(
                    "Pointer-valued assignments must have exactly one target."
                )
            return
        out.append(
            NAssign(targets=stmt.targets, target_names=stmt.target_names, expr=value)
        )
        return

    if isinstance(stmt, NExprEffect):
        if isinstance(stmt.expr, NBuiltinCall) and stmt.expr.op == "mstore8":
            raise LoweringError("mstore8 is forbidden by the memory model.")
        if (
            isinstance(stmt.expr, NBuiltinCall)
            and stmt.expr.op == "mstore"
            and len(stmt.expr.args) == 2
        ):
            addr = _resolve_addr(stmt.expr.args[0], "mstore", ctx.mem, env)
            _emit_store(
                addr=addr, value_expr=stmt.expr.args[1], ctx=ctx, env=env, out=out
            )
            return
        if (
            isinstance(stmt.expr, NBuiltinCall)
            and stmt.expr.op == "mload"
            and len(stmt.expr.args) == 1
        ):
            ctx.mem.load(
                _resolve_addr(stmt.expr.args[0], "mload", ctx.mem, env), op="mload"
            )
            return
        out.append(NExprEffect(expr=_resolve_word_expr(stmt.expr, ctx.mem, env)))
        return

    if isinstance(stmt, NIf):
        new_cond = _resolve_word_expr(stmt.condition, ctx.mem, env)
        cond_truthy = const_truthy(new_cond)
        if cond_truthy is not None:
            if not cond_truthy:
                return
            lowered_then = _lower_block(stmt.then_body, ctx, env)
            if lowered_then.defs or lowered_then.stmts:
                out.append(lowered_then)
            return

        _reject_memory_writes_in_block(stmt.then_body, "if-body")
        before_env = env.copy()
        then_env = env.copy()
        then_body = _lower_block(stmt.then_body, ctx, then_env)
        env.update_from(_join_fact_envs([before_env, then_env]))
        out.append(NIf(condition=new_cond, then_body=then_body))
        return

    if isinstance(stmt, NSwitch):
        new_disc = _resolve_word_expr(stmt.discriminant, ctx.mem, env)
        disc_value = const_value(new_disc)
        if disc_value is not None:
            for case in stmt.cases:
                if case.value.value == disc_value:
                    lowered_case = _lower_block(case.body, ctx, env)
                    if lowered_case.defs or lowered_case.stmts:
                        out.append(lowered_case)
                    return
            if stmt.default is not None:
                lowered_default = _lower_block(stmt.default, ctx, env)
                if lowered_default.defs or lowered_default.stmts:
                    out.append(lowered_default)
            return

        for case in stmt.cases:
            _reject_memory_writes_in_block(case.body, "switch-case")
        if stmt.default is not None:
            _reject_memory_writes_in_block(stmt.default, "switch-default")
        branch_envs: list[_FactEnv] = []
        new_cases: list[NSwitchCase] = []
        for case in stmt.cases:
            case_env = env.copy()
            branch_envs.append(case_env)
            new_cases.append(
                NSwitchCase(
                    value=case.value, body=_lower_block(case.body, ctx, case_env)
                )
            )
        new_default = None
        if stmt.default is not None:
            default_env = env.copy()
            branch_envs.append(default_env)
            new_default = _lower_block(stmt.default, ctx, default_env)
        else:
            branch_envs.append(env.copy())
        env.update_from(_join_fact_envs(branch_envs))
        out.append(
            NSwitch(discriminant=new_disc, cases=tuple(new_cases), default=new_default)
        )
        return

    if isinstance(stmt, NFor):
        raise LoweringError(
            "NFor reached memory lowering. The staged pipeline should reject "
            "for-loops before memory lowering."
        )

    if isinstance(stmt, NLeave):
        out.append(stmt)
        return

    if isinstance(stmt, NBlock):
        out.append(_lower_block(stmt, ctx, env))
        return

    assert_never(stmt)


def lower_memory(func: NormalizedFunction) -> NormalizedFunction:
    """Resolve helper-free normalized-IR memory operations into direct value flow."""
    if collect_function_defs(func.body):
        raise LoweringError(
            "Nested helper definitions reached memory lowering. "
            "Seal the helper boundary after inlining and before memory lowering."
        )
    residual_call = first_runtime_local_call(func.body)
    if residual_call is not None:
        raise LoweringError(
            f"Residual local helper call {residual_call.name!r} reached memory "
            "lowering. Seal the helper boundary after inlining and before "
            "memory lowering."
        )
    ctx = _MemCtx(next_id=max_symbol_id(func) + 1)
    env = _FactEnv()
    new_body = _lower_block(func.body, ctx, env)
    for sid, name in zip(func.returns, func.return_names):
        if env.is_tainted(sid):
            raise LoweringError(
                f"Return value {name!r} may still hold a free-pointer value."
            )
    return NormalizedFunction(
        name=func.name,
        params=func.params,
        param_names=func.param_names,
        returns=func.returns,
        return_names=func.return_names,
        body=new_body,
    )
