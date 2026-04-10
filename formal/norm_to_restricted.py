"""
Lower normalized imperative IR to non-SSA restricted IR.

Merges handoff Passes 7 (memory model lowering) and 8 (restricted IR
construction) into one step.  Memory legality falls out of the
``MemoryState.join`` operation rather than ad-hoc syntax inspection.

After this pass:
- All memory operations are resolved (no mstore/mload/NStore)
- Control flow is explicit ``RConditionalBlock`` with branch outputs
- For-loops are rejected (must be eliminated by earlier passes)
- Output is a flat sequence of ``RAssignment`` / ``RConditionalBlock``
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
    NTopLevelCall,
    NUnresolvedCall,
)
from norm_walk import map_expr
from restricted_ir import (
    RAssignment,
    RBranch,
    RBuiltinCall,
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

# ---------------------------------------------------------------------------
# SymbolId allocator (for memory snapshot temps and branch outputs)
# ---------------------------------------------------------------------------


class _Alloc:
    def __init__(self, start: int) -> None:
        self._next = start

    def alloc(self) -> SymbolId:
        sid = SymbolId(self._next)
        self._next += 1
        return sid


# ---------------------------------------------------------------------------
# Memory state (analysis, not syntax)
# ---------------------------------------------------------------------------


@dataclass
class MemoryState:
    """Tracks memory slots as SymbolId → stored value bindings.

    Stored values are always SymbolIds (bound to temps at store time),
    making snapshot semantics implicit and join well-defined.
    """

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

    def join(self, other: MemoryState) -> None:
        """Join another branch's memory state into this one.

        Rejects if either branch wrote to a slot the other didn't
        (asymmetric writes are not supported in the restricted model).
        """
        for addr in other.slots:
            if addr not in self.slots:
                raise ParseError(
                    f"Memory write to address {addr} inside conditional branch. "
                    f"The memory model requires straight-line writes."
                )
        for addr in self.slots:
            if addr not in other.slots:
                # Slot exists in pre-if state but other branch didn't write —
                # that's fine, the pre-if value is still valid.
                pass


# ---------------------------------------------------------------------------
# Address validation
# ---------------------------------------------------------------------------


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


# ---------------------------------------------------------------------------
# NExpr → RExpr conversion
# ---------------------------------------------------------------------------


def _lower_expr(expr: NExpr, mem: MemoryState) -> RExpr:
    """Convert a normalized expression to restricted IR, resolving mload."""
    if isinstance(expr, NConst):
        return RConst(value=expr.value)

    if isinstance(expr, NRef):
        return RRef(symbol_id=expr.symbol_id, name=expr.name)

    if isinstance(expr, NBuiltinCall):
        # mload: resolve from memory state.
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


# ---------------------------------------------------------------------------
# Block lowering
# ---------------------------------------------------------------------------


def _lower_block(
    block: NBlock,
    mem: MemoryState,
    alloc: _Alloc,
    var_state: dict[SymbolId, bool],
) -> list[RStatement]:
    """Lower a normalized block to restricted IR statements.

    *var_state* tracks which SymbolIds have been assigned (for
    detecting which variables are modified in a branch).
    """
    out: list[RStatement] = []
    for stmt in block.stmts:
        _lower_stmt(stmt, mem, alloc, var_state, out)
    return out


def _lower_stmt(
    stmt: NStmt,
    mem: MemoryState,
    alloc: _Alloc,
    var_state: dict[SymbolId, bool],
    out: list[RStatement],
) -> None:
    if isinstance(stmt, NStore):
        addr = _resolve_const_addr(stmt.addr, "mstore")
        # Snapshot: bind value to a fresh temp.
        rvalue = _lower_expr(stmt.value, mem)
        tid = alloc.alloc()
        out.append(RAssignment(target=tid, target_name=f"_mem_{addr}", expr=rvalue))
        mem.store(addr, tid)
        return

    if isinstance(stmt, NExprEffect):
        # Bare mstore from Yul source.
        if (
            isinstance(stmt.expr, NBuiltinCall)
            and stmt.expr.op == "mstore"
            and len(stmt.expr.args) == 2
        ):
            addr = _resolve_const_addr(stmt.expr.args[0], "mstore")
            rvalue = _lower_expr(stmt.expr.args[1], mem)
            tid = alloc.alloc()
            out.append(RAssignment(target=tid, target_name=f"_mem_{addr}", expr=rvalue))
            mem.store(addr, tid)
            return
        # Other expression-statements: just lower the expression.
        # (They have no target, so emit nothing — the expression is
        # for side effects only, which should have been eliminated.)
        return

    if isinstance(stmt, (NBind, NAssign)):
        expr = stmt.expr
        if isinstance(stmt, NBind) and expr is None:
            # Bare let — zero-init each target.
            for sid, name in zip(stmt.targets, stmt.target_names):
                out.append(RAssignment(target=sid, target_name=name, expr=RConst(0)))
                var_state[sid] = True
            return
        assert expr is not None
        rexpr = _lower_expr(expr, mem)
        if len(stmt.targets) == 1:
            sid = stmt.targets[0]
            name = stmt.target_names[0]
            out.append(RAssignment(target=sid, target_name=name, expr=rexpr))
            var_state[sid] = True
        else:
            # Multi-target: should have been split by inliner.
            # If still present, lower each target separately.
            for sid, name in zip(stmt.targets, stmt.target_names):
                out.append(RAssignment(target=sid, target_name=name, expr=rexpr))
                var_state[sid] = True
        return

    if isinstance(stmt, NIf):
        _lower_if(stmt, mem, alloc, var_state, out)
        return

    if isinstance(stmt, NSwitch):
        # Lower switch to nested conditionals.
        _lower_switch(stmt, mem, alloc, var_state, out)
        return

    if isinstance(stmt, NBlock):
        nested = _lower_block(stmt, mem, alloc, var_state)
        out.extend(nested)
        return

    if isinstance(stmt, NFunctionDef):
        # Structural — skip in restricted IR.
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
    var_state: dict[SymbolId, bool],
    out: list[RStatement],
) -> None:
    """Lower an NIf to an RConditionalBlock with explicit outputs."""
    cond = _lower_expr(stmt.condition, mem)

    # Lower then-branch under copied state.
    then_mem = mem.copy()
    then_var: dict[SymbolId, bool] = {}
    then_stmts = _lower_block(stmt.then_body, then_mem, alloc, then_var)

    # Join memory states.
    mem.join(then_mem)

    # Determine which variables were modified in the then-branch.
    modified_sids = [sid for sid in then_var]
    if not modified_sids and not then_stmts:
        return

    # output_vars = the original variable SymbolIds that get new values.
    # then_branch.outputs = which variables in the then-scope provide values.
    # else_branch.outputs = same original SymbolIds (pre-if values).
    output_names: list[str] = []
    for sid in modified_sids:
        output_names.append(_find_name_for_sid(sid, then_stmts))

    then_branch = RBranch(
        assignments=tuple(then_stmts),
        outputs=tuple(modified_sids),  # Then: the modified values.
    )
    else_branch = RBranch(
        assignments=(),  # Else: no assignments.
        outputs=tuple(modified_sids),  # Else: pre-if values (same sids).
    )

    out.append(
        RConditionalBlock(
            condition=cond,
            output_vars=tuple(modified_sids),
            output_names=tuple(output_names),
            then_branch=then_branch,
            else_branch=else_branch,
        )
    )

    for sid in modified_sids:
        var_state[sid] = True


def _lower_switch(
    stmt: NSwitch,
    mem: MemoryState,
    alloc: _Alloc,
    var_state: dict[SymbolId, bool],
    out: list[RStatement],
) -> None:
    """Lower NSwitch to nested RConditionalBlock chain."""
    disc = _lower_expr(stmt.discriminant, mem)

    # For each case, build an NIf-like conditional.
    # Process from last case to first, building a chain.
    # For now, convert to nested NIf and lower recursively.
    # This reuses the NIf lowering logic.

    # Build from bottom up: default (or empty) as the else.
    if stmt.default is not None:
        default_stmts = _lower_block(stmt.default, mem.copy(), alloc, dict(var_state))
    else:
        default_stmts = []

    # For single-case + default (the common Yul pattern):
    if len(stmt.cases) == 1:
        case = stmt.cases[0]
        case_cond: RExpr = RBuiltinCall(op="eq", args=(disc, RConst(case.value.value)))
        then_mem = mem.copy()
        then_var: dict[SymbolId, bool] = {}
        then_stmts = _lower_block(case.body, then_mem, alloc, then_var)
        mem.join(then_mem)

        modified = list(then_var.keys())
        output_sids: list[SymbolId] = []
        output_names: list[str] = []
        then_outputs: list[SymbolId] = []
        else_outputs: list[SymbolId] = []

        for sid in modified:
            out_sid = alloc.alloc()
            output_sids.append(out_sid)
            output_names.append(_find_name_for_sid(sid, then_stmts))
            then_outputs.append(sid)
            else_outputs.append(sid)

        out.append(
            RConditionalBlock(
                condition=case_cond,
                output_vars=tuple(output_sids),
                output_names=tuple(output_names),
                then_branch=RBranch(
                    assignments=tuple(then_stmts), outputs=tuple(then_outputs)
                ),
                else_branch=RBranch(
                    assignments=tuple(default_stmts), outputs=tuple(else_outputs)
                ),
            )
        )
        for sid in output_sids:
            var_state[sid] = True
        return

    # General multi-case: reject for now (rare in supported Yul subset).
    raise ParseError(
        f"Multi-case switch ({len(stmt.cases)} cases) not yet supported "
        f"in restricted IR lowering"
    )


def _find_name_for_sid(sid: SymbolId, stmts: list[RStatement]) -> str:
    """Find the target_name for a SymbolId from a list of assignments."""
    for stmt in stmts:
        if isinstance(stmt, RAssignment) and stmt.target == sid:
            return stmt.target_name
    return f"_v_{sid._id}"


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def lower_to_restricted(func: NormalizedFunction) -> RestrictedFunction:
    """Lower normalized IR to non-SSA restricted IR with memory elimination.

    All memory operations are resolved to direct value references.
    Control flow becomes explicit ``RConditionalBlock`` with branch
    outputs.  For-loops and unresolved local calls are rejected.
    """
    from norm_walk import max_symbol_id

    alloc = _Alloc(max_symbol_id(func) + 1)
    mem = MemoryState()
    var_state: dict[SymbolId, bool] = {}

    # Mark params and returns as existing.
    for sid in func.params:
        var_state[sid] = True
    for sid in func.returns:
        var_state[sid] = True

    body = _lower_block(func.body, mem, alloc, var_state)

    return RestrictedFunction(
        name=func.name,
        params=func.params,
        param_names=func.param_names,
        returns=func.returns,
        return_names=func.return_names,
        body=tuple(body),
    )
