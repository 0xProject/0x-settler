"""
Lower normalized imperative IR to non-SSA restricted IR.

This pass performs memory elimination plus restricted-IR construction.
The resulting IR has:

- no memory operations
- explicit conditional outputs
- direct model-call assignments for top-level calls
- no SSA renaming
"""

from __future__ import annotations

from dataclasses import dataclass, field

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
    NIte,
    NLeave,
    NLocalCall,
    NormalizedFunction,
    NRef,
    NStmt,
    NStore,
    NSwitch,
    NSwitchCase,
    NTopLevelCall,
    NUnresolvedCall,
)
from norm_walk import for_each_expr, max_symbol_id
from restricted_ir import (
    RAssignment,
    RBranch,
    RBuiltinCall,
    RCallAssign,
    RConditionalBlock,
    RConst,
    RestrictedFunction,
    RExpr,
    RIte,
    RModelCall,
    RRef,
    RStatement,
)
from yul_ast import ParseError, SymbolId


class _Alloc:
    def __init__(self, start: int) -> None:
        self._next = start

    def alloc(self) -> SymbolId:
        sid = SymbolId(self._next)
        self._next += 1
        return sid


@dataclass
class MemoryState:
    """Straight-line memory state keyed by constant addresses."""

    slots: dict[int, SymbolId] = field(default_factory=dict)

    def store(self, addr: int, value_sid: SymbolId) -> None:
        if addr in self.slots:
            raise ParseError(
                f"Duplicate mstore to address {addr}. "
                f"The memory model forbids aliasing or overwriting."
            )
        self.slots[addr] = value_sid

    def load(self, addr: int) -> SymbolId:
        if addr not in self.slots:
            available = sorted(self.slots.keys())
            raise ParseError(
                f"mload from address {addr} with no prior mstore. "
                f"Available: {available}"
            )
        return self.slots[addr]

    def copy(self) -> MemoryState:
        return MemoryState(slots=dict(self.slots))


def _resolve_const_addr(expr: NExpr, op: str) -> int:
    folded = fold_expr(expr)
    if not isinstance(folded, NConst):
        raise ParseError(
            f"Non-constant {op} address: {expr!r}. "
            f"The memory model requires constant 32-byte-aligned addresses."
        )
    addr = folded.value
    if addr % 32 != 0:
        raise ParseError(f"Unaligned {op} address {addr} (must be 32-byte aligned)")
    return addr


def _expr_has_memory_op(expr: NExpr) -> bool:
    found = False

    def check(e: NExpr) -> None:
        nonlocal found
        if isinstance(e, NBuiltinCall) and e.op in ("mload", "mstore"):
            found = True

    for_each_expr(expr, check)
    return found


def _reject_memory_ops_in_block(block: NBlock, context: str) -> None:
    """Reject memory ops anywhere inside nested control-flow bodies."""
    for stmt in block.stmts:
        if isinstance(stmt, NStore):
            raise ParseError(
                f"Memory operation inside conditional ({context}). "
                f"The restricted memory model requires straight-line memory."
            )
        if isinstance(stmt, NExprEffect):
            if _expr_has_memory_op(stmt.expr):
                raise ParseError(
                    f"Memory operation inside conditional ({context}). "
                    f"The restricted memory model requires straight-line memory."
                )
            continue
        if isinstance(stmt, (NBind, NAssign)):
            if stmt.expr is not None and _expr_has_memory_op(stmt.expr):
                raise ParseError(
                    f"Memory operation inside conditional ({context}). "
                    f"The restricted memory model requires straight-line memory."
                )
            continue
        if isinstance(stmt, NIf):
            if _expr_has_memory_op(stmt.condition):
                raise ParseError(
                    f"Memory operation inside conditional ({context}). "
                    f"The restricted memory model requires straight-line memory."
                )
            _reject_memory_ops_in_block(stmt.then_body, context)
            continue
        if isinstance(stmt, NSwitch):
            if _expr_has_memory_op(stmt.discriminant):
                raise ParseError(
                    f"Memory operation inside conditional ({context}). "
                    f"The restricted memory model requires straight-line memory."
                )
            for case in stmt.cases:
                _reject_memory_ops_in_block(case.body, context)
            if stmt.default is not None:
                _reject_memory_ops_in_block(stmt.default, context)
            continue
        if isinstance(stmt, NFor):
            if _expr_has_memory_op(stmt.condition):
                raise ParseError(
                    f"Memory operation inside conditional ({context}). "
                    f"The restricted memory model requires straight-line memory."
                )
            _reject_memory_ops_in_block(stmt.init, context)
            if stmt.condition_setup is not None:
                _reject_memory_ops_in_block(stmt.condition_setup, context)
            _reject_memory_ops_in_block(stmt.post, context)
            _reject_memory_ops_in_block(stmt.body, context)
            continue
        if isinstance(stmt, NBlock):
            _reject_memory_ops_in_block(stmt, context)


def _name_for_sid(sid: SymbolId, names: dict[SymbolId, str]) -> str:
    return names.get(sid, f"_v_{sid._id}")


def _lower_expr(expr: NExpr, mem: MemoryState) -> RExpr:
    if isinstance(expr, NConst):
        return RConst(value=expr.value)

    if isinstance(expr, NRef):
        return RRef(symbol_id=expr.symbol_id, name=expr.name)

    if isinstance(expr, NBuiltinCall):
        if expr.op == "mload" and len(expr.args) == 1:
            addr = _resolve_const_addr(expr.args[0], "mload")
            sid = mem.load(addr)
            return RRef(symbol_id=sid, name=f"_mem_{addr}")
        args = tuple(_lower_expr(a, mem) for a in expr.args)
        return RBuiltinCall(op=expr.op, args=args)

    if isinstance(expr, NLocalCall):
        raise ParseError(
            f"Unresolved local call to {expr.name!r} in restricted IR lowering. "
            f"All helpers should be inlined before this pass."
        )

    if isinstance(expr, NTopLevelCall):
        args = tuple(_lower_expr(a, mem) for a in expr.args)
        return RModelCall(name=expr.name, args=args)

    if isinstance(expr, NUnresolvedCall):
        raise ParseError(f"Unresolved call to {expr.name!r} in restricted IR lowering")

    if isinstance(expr, NIte):
        return RIte(
            cond=_lower_expr(expr.cond, mem),
            if_true=_lower_expr(expr.if_true, mem),
            if_false=_lower_expr(expr.if_false, mem),
        )

    raise ParseError(f"Unexpected expression: {type(expr).__name__}")


def _emit_memory_store(
    *,
    addr: int,
    value_expr: NExpr,
    mem: MemoryState,
    alloc: _Alloc,
    out: list[RStatement],
    names: dict[SymbolId, str],
) -> None:
    rvalue = _lower_expr(value_expr, mem)
    tid = alloc.alloc()
    name = f"_mem_{addr}"
    names[tid] = name
    out.append(RAssignment(target=tid, target_name=name, expr=rvalue))
    mem.store(addr, tid)


def _modified_union(
    outer_order: tuple[SymbolId, ...],
    then_var: dict[SymbolId, bool],
    else_var: dict[SymbolId, bool],
) -> list[SymbolId]:
    return [sid for sid in outer_order if sid in then_var or sid in else_var]


def _build_conditional(
    *,
    condition: RExpr,
    then_assignments: list[RStatement],
    then_var: dict[SymbolId, bool],
    else_assignments: list[RStatement],
    else_var: dict[SymbolId, bool],
    outer_order: tuple[SymbolId, ...],
    names: dict[SymbolId, str],
) -> tuple[RConditionalBlock | None, list[SymbolId]]:
    output_targets = _modified_union(outer_order, then_var, else_var)
    if not output_targets:
        return None, []

    output_names = tuple(_name_for_sid(sid, names) for sid in output_targets)
    branch_outputs = tuple(
        RRef(symbol_id=sid, name=_name_for_sid(sid, names)) for sid in output_targets
    )
    return (
        RConditionalBlock(
            condition=condition,
            output_targets=tuple(output_targets),
            output_names=output_names,
            then_branch=RBranch(
                assignments=tuple(then_assignments),
                output_exprs=branch_outputs,
            ),
            else_branch=RBranch(
                assignments=tuple(else_assignments),
                output_exprs=branch_outputs,
            ),
        ),
        output_targets,
    )


def _lower_block(
    block: NBlock,
    mem: MemoryState,
    alloc: _Alloc,
    names: dict[SymbolId, str],
    visible_state: dict[SymbolId, bool],
    modified_state: dict[SymbolId, bool],
) -> list[RStatement]:
    out: list[RStatement] = []
    for stmt in block.stmts:
        _lower_stmt(stmt, mem, alloc, names, visible_state, modified_state, out)
    return out


def _lower_stmt(
    stmt: NStmt,
    mem: MemoryState,
    alloc: _Alloc,
    names: dict[SymbolId, str],
    visible_state: dict[SymbolId, bool],
    modified_state: dict[SymbolId, bool],
    out: list[RStatement],
) -> None:
    if isinstance(stmt, NStore):
        addr = _resolve_const_addr(stmt.addr, "mstore")
        _emit_memory_store(
            addr=addr,
            value_expr=stmt.value,
            mem=mem,
            alloc=alloc,
            out=out,
            names=names,
        )
        return

    if isinstance(stmt, NExprEffect):
        if (
            isinstance(stmt.expr, NBuiltinCall)
            and stmt.expr.op == "mstore"
            and len(stmt.expr.args) == 2
        ):
            addr = _resolve_const_addr(stmt.expr.args[0], "mstore")
            _emit_memory_store(
                addr=addr,
                value_expr=stmt.expr.args[1],
                mem=mem,
                alloc=alloc,
                out=out,
                names=names,
            )
        return

    if isinstance(stmt, (NBind, NAssign)):
        expr = stmt.expr
        if isinstance(stmt, NBind) and expr is None:
            for sid, name in zip(stmt.targets, stmt.target_names):
                names[sid] = name
                out.append(RAssignment(target=sid, target_name=name, expr=RConst(0)))
                visible_state[sid] = True
                modified_state[sid] = True
            return

        assert expr is not None
        if isinstance(expr, NTopLevelCall):
            args = tuple(_lower_expr(a, mem) for a in expr.args)
            for sid, name in zip(stmt.targets, stmt.target_names):
                names[sid] = name
                visible_state[sid] = True
                modified_state[sid] = True
            out.append(
                RCallAssign(
                    targets=stmt.targets,
                    target_names=stmt.target_names,
                    callee=expr.name,
                    args=args,
                )
            )
            return

        if len(stmt.targets) > 1:
            raise ParseError(
                "Multi-target assignment in restricted IR lowering requires "
                "a top-level model call"
            )

        rexpr = _lower_expr(expr, mem)
        sid = stmt.targets[0]
        name = stmt.target_names[0]
        names[sid] = name
        out.append(RAssignment(target=sid, target_name=name, expr=rexpr))
        visible_state[sid] = True
        modified_state[sid] = True
        return

    if isinstance(stmt, NIf):
        _lower_if(stmt, mem, alloc, names, visible_state, modified_state, out)
        return

    if isinstance(stmt, NSwitch):
        _lower_switch(stmt, mem, alloc, names, visible_state, modified_state, out)
        return

    if isinstance(stmt, NBlock):
        out.extend(_lower_block(stmt, mem, alloc, names, visible_state, modified_state))
        return

    if isinstance(stmt, NFunctionDef):
        return

    if isinstance(stmt, NLeave):
        raise ParseError("NLeave in restricted IR lowering — should have been inlined")

    if isinstance(stmt, NFor):
        raise ParseError("NFor in restricted IR lowering — not supported")

    raise ParseError(f"Unexpected statement: {type(stmt).__name__}")


def _lower_if(
    stmt: NIf,
    mem: MemoryState,
    alloc: _Alloc,
    names: dict[SymbolId, str],
    visible_state: dict[SymbolId, bool],
    modified_state: dict[SymbolId, bool],
    out: list[RStatement],
) -> None:
    _reject_memory_ops_in_block(stmt.then_body, "if-body")

    cond = _lower_expr(stmt.condition, mem)
    outer_order = tuple(visible_state.keys())

    then_mem = mem.copy()
    then_visible = dict(visible_state)
    then_modified: dict[SymbolId, bool] = {}
    then_assignments = _lower_block(
        stmt.then_body, then_mem, alloc, names, then_visible, then_modified
    )

    conditional, outputs = _build_conditional(
        condition=cond,
        then_assignments=then_assignments,
        then_var=then_modified,
        else_assignments=[],
        else_var={},
        outer_order=outer_order,
        names=names,
    )
    if conditional is not None:
        out.append(conditional)
        for sid in outputs:
            visible_state[sid] = True
            modified_state[sid] = True


def _lower_switch_chain(
    *,
    disc: RExpr,
    cases: tuple[NSwitchCase, ...],
    default: NBlock | None,
    mem: MemoryState,
    alloc: _Alloc,
    names: dict[SymbolId, str],
    outer_order: tuple[SymbolId, ...],
    visible_state: dict[SymbolId, bool],
) -> tuple[list[RStatement], dict[SymbolId, bool]]:
    if not cases:
        if default is None:
            return [], {}
        default_mem = mem.copy()
        default_visible = dict(visible_state)
        default_modified: dict[SymbolId, bool] = {}
        default_assignments = _lower_block(
            default, default_mem, alloc, names, default_visible, default_modified
        )
        return default_assignments, default_modified

    case = cases[0]
    then_mem = mem.copy()
    then_visible = dict(visible_state)
    then_modified: dict[SymbolId, bool] = {}
    then_assignments = _lower_block(
        case.body, then_mem, alloc, names, then_visible, then_modified
    )

    else_assignments, else_var = _lower_switch_chain(
        disc=disc,
        cases=cases[1:],
        default=default,
        mem=mem.copy(),
        alloc=alloc,
        names=names,
        outer_order=outer_order,
        visible_state=visible_state,
    )

    condition = RBuiltinCall(op="eq", args=(disc, RConst(case.value.value)))
    conditional, outputs = _build_conditional(
        condition=condition,
        then_assignments=then_assignments,
        then_var=then_modified,
        else_assignments=else_assignments,
        else_var=else_var,
        outer_order=outer_order,
        names=names,
    )
    if conditional is None:
        return else_assignments, else_var
    return [conditional], {sid: True for sid in outputs}


def _lower_switch(
    stmt: NSwitch,
    mem: MemoryState,
    alloc: _Alloc,
    names: dict[SymbolId, str],
    visible_state: dict[SymbolId, bool],
    modified_state: dict[SymbolId, bool],
    out: list[RStatement],
) -> None:
    for case in stmt.cases:
        _reject_memory_ops_in_block(case.body, "switch-case")
    if stmt.default is not None:
        _reject_memory_ops_in_block(stmt.default, "switch-default")

    disc = _lower_expr(stmt.discriminant, mem)
    outer_order = tuple(visible_state.keys())

    chain_assignments, chain_var = _lower_switch_chain(
        disc=disc,
        cases=stmt.cases,
        default=stmt.default,
        mem=mem,
        alloc=alloc,
        names=names,
        outer_order=outer_order,
        visible_state=visible_state,
    )
    out.extend(chain_assignments)
    for sid in chain_var:
        visible_state[sid] = True
        modified_state[sid] = True


def lower_to_restricted(func: NormalizedFunction) -> RestrictedFunction:
    """Lower normalized IR to non-SSA restricted IR with memory elimination."""
    alloc = _Alloc(max_symbol_id(func) + 1)
    mem = MemoryState()
    names: dict[SymbolId, str] = {}
    var_state: dict[SymbolId, bool] = {}

    for sid, name in zip(func.params, func.param_names):
        names[sid] = name
        var_state[sid] = True
    for sid, name in zip(func.returns, func.return_names):
        names[sid] = name
        var_state[sid] = True

    body = _lower_block(func.body, mem, alloc, names, var_state, {})

    return RestrictedFunction(
        name=func.name,
        params=func.params,
        param_names=func.param_names,
        returns=func.returns,
        return_names=func.return_names,
        body=tuple(body),
    )
