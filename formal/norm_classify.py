"""
Per-function effect analysis and inlining classification for normalized IR.

Walks a ``NormalizedFunction`` to determine each nested helper's effects
(memory, leave, for-loops, expression-statements) and classifies them
for inlining: pure (safe to expression-substitute), deferred (has
memory effects), or unsupported.

This replaces the old pipeline's distributed logic in
``_classify_non_pure_helpers()``, ``_is_uint512_from_helper()``,
and ``_reject_expr_stmts()``.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import assert_never

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
    NSwitch,
    NTopLevelCall,
    NUnresolvedCall,
)
from yul_ast import SymbolId

# ---------------------------------------------------------------------------
# Memory op names — recognized regardless of call classification
# ---------------------------------------------------------------------------

_MEMORY_WRITE_OPS: frozenset[str] = frozenset({"mstore", "mstore8"})
_MEMORY_READ_OPS: frozenset[str] = frozenset({"mload"})

# ---------------------------------------------------------------------------
# Per-function summary (local, no call-graph)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class FunctionSummary:
    """Per-function analysis of effects and structure."""

    writes_memory: bool
    reads_memory: bool
    may_leave: bool
    has_for_loop: bool
    has_expr_effects: bool
    has_effectful_condition: bool
    calls_unresolved: bool
    calls_top_level: bool
    called_functions: frozenset[SymbolId]
    called_builtins: frozenset[str]
    is_uint512_from: bool


def summarize_function(body: NBlock) -> FunctionSummary:
    """Analyze a function body for effects (non-recursive into nested defs)."""
    acc = _SummaryAccumulator()
    _walk_block(acc, body)
    return FunctionSummary(
        writes_memory=acc.writes_memory,
        reads_memory=acc.reads_memory,
        may_leave=acc.may_leave,
        has_for_loop=acc.has_for_loop,
        has_expr_effects=acc.has_expr_effects,
        has_effectful_condition=acc.has_effectful_condition,
        calls_unresolved=acc.calls_unresolved,
        calls_top_level=acc.calls_top_level,
        called_functions=frozenset(acc.called_functions),
        called_builtins=frozenset(acc.called_builtins),
        is_uint512_from=False,  # set separately by caller
    )


class _SummaryAccumulator:
    """Mutable accumulator for the summary walk."""

    def __init__(self) -> None:
        self.writes_memory: bool = False
        self.reads_memory: bool = False
        self.may_leave: bool = False
        self.has_for_loop: bool = False
        self.has_expr_effects: bool = False
        self.has_effectful_condition: bool = False
        self.calls_unresolved: bool = False
        self.calls_top_level: bool = False
        self.called_functions: set[SymbolId] = set()
        self.called_builtins: set[str] = set()


def _walk_block(acc: _SummaryAccumulator, block: NBlock) -> None:
    for stmt in block.stmts:
        _walk_stmt(acc, stmt)


def _walk_stmt(acc: _SummaryAccumulator, stmt: NStmt) -> None:
    if isinstance(stmt, NBind):
        if stmt.expr is not None:
            _walk_expr(acc, stmt.expr)
    elif isinstance(stmt, NAssign):
        _walk_expr(acc, stmt.expr)
    elif isinstance(stmt, NExprEffect):
        # mstore/mload as expression-statements are normal memory ops,
        # NOT unsupported expression-statements.
        if not _is_known_effect_call(stmt.expr):
            acc.has_expr_effects = True
        _walk_expr(acc, stmt.expr)
    elif isinstance(stmt, NIf):
        if _has_call_in_expr(stmt.condition):
            acc.has_effectful_condition = True
        _walk_expr(acc, stmt.condition)
        _walk_block(acc, stmt.then_body)
    elif isinstance(stmt, NSwitch):
        if _has_call_in_expr(stmt.discriminant):
            acc.has_effectful_condition = True
        _walk_expr(acc, stmt.discriminant)
        for case in stmt.cases:
            _walk_block(acc, case.body)
        if stmt.default is not None:
            _walk_block(acc, stmt.default)
    elif isinstance(stmt, NFor):
        acc.has_for_loop = True
        if _has_call_in_expr(stmt.condition):
            acc.has_effectful_condition = True
        _walk_block(acc, stmt.init)
        _walk_expr(acc, stmt.condition)
        _walk_block(acc, stmt.post)
        _walk_block(acc, stmt.body)
    elif isinstance(stmt, NLeave):
        acc.may_leave = True
    elif isinstance(stmt, NBlock):
        _walk_block(acc, stmt)
    elif isinstance(stmt, NFunctionDef):
        # Do NOT recurse into nested function bodies — they get
        # their own summary.
        pass


def _has_call_in_expr(expr: NExpr) -> bool:
    """Check if an expression contains any function call (local/top-level/unresolved).

    Used to detect effectful control-flow conditions.  Builtin calls
    (EVM opcodes) are pure and do not count.
    """
    if isinstance(expr, (NConst, NRef)):
        return False
    if isinstance(expr, NBuiltinCall):
        return any(_has_call_in_expr(a) for a in expr.args)
    if isinstance(expr, (NLocalCall, NTopLevelCall, NUnresolvedCall)):
        return True
    if isinstance(expr, NIte):
        return (
            _has_call_in_expr(expr.cond)
            or _has_call_in_expr(expr.if_true)
            or _has_call_in_expr(expr.if_false)
        )
    assert_never(expr)


def _walk_expr(acc: _SummaryAccumulator, expr: NExpr) -> None:
    if isinstance(expr, (NConst, NRef)):
        pass
    elif isinstance(expr, NBuiltinCall):
        acc.called_builtins.add(expr.op)
        if expr.op in _MEMORY_WRITE_OPS:
            acc.writes_memory = True
        if expr.op in _MEMORY_READ_OPS:
            acc.reads_memory = True
        for a in expr.args:
            _walk_expr(acc, a)
    elif isinstance(expr, NLocalCall):
        acc.called_functions.add(expr.symbol_id)
        for a in expr.args:
            _walk_expr(acc, a)
    elif isinstance(expr, NTopLevelCall):
        acc.calls_top_level = True
        for a in expr.args:
            _walk_expr(acc, a)
    elif isinstance(expr, NUnresolvedCall):
        acc.calls_unresolved = True
        for a in expr.args:
            _walk_expr(acc, a)
    elif isinstance(expr, NIte):
        _walk_expr(acc, expr.cond)
        _walk_expr(acc, expr.if_true)
        _walk_expr(acc, expr.if_false)


def _is_known_effect_call(expr: NExpr) -> bool:
    """Check if an expression-statement is a known effect pattern.

    Function calls (local, top-level) as bare statements are valid
    void calls for side effects.  Memory builtins (mstore) are also
    valid.  Only pure builtins with no side effects (e.g. bare
    ``add(x, 1)``) are truly unsupported expression-statements.
    """
    if isinstance(expr, NBuiltinCall):
        return expr.op in _MEMORY_WRITE_OPS or expr.op in _MEMORY_READ_OPS
    return isinstance(expr, (NLocalCall, NTopLevelCall, NUnresolvedCall))


# ---------------------------------------------------------------------------
# uint512.from shape detection
# ---------------------------------------------------------------------------


def _is_uint512_from_shape(
    fdef: NFunctionDef,
) -> bool:
    """Check if a function definition matches the exact uint512.from pattern.

    Expected shape (3 params, 1 return, 4-5 statements):
        [optional: let tmp := 0]
        ret := 0  (or ret := tmp)
        mstore(ptr, hi)
        mstore(add(0x20, ptr) or add(ptr, 0x20), lo)
        ret := ptr
    """
    if len(fdef.params) != 3 or len(fdef.returns) != 1:
        return False

    stmts = fdef.body.stmts
    # Filter out NFunctionDef nodes (shouldn't be there, but be safe).
    real_stmts: list[NStmt] = [s for s in stmts if not isinstance(s, NFunctionDef)]

    if len(real_stmts) not in (4, 5):
        return False

    ptr_id = fdef.params[0]
    hi_id = fdef.params[1]
    lo_id = fdef.params[2]
    ret_id = fdef.returns[0]

    if len(real_stmts) == 5:
        # 5-stmt form: let tmp := 0, ret := tmp, mstore(ptr, hi), mstore(ptr+32, lo), ret := ptr
        zero_init = real_stmts[0]
        init_ret = real_stmts[1]
        write_hi = real_stmts[2]
        write_lo = real_stmts[3]
        ret_assign = real_stmts[4]

        if not isinstance(zero_init, NBind) or zero_init.expr is None:
            return False
        if not _is_zero(zero_init.expr):
            return False
    else:
        # 4-stmt form: ret := 0, mstore(ptr, hi), mstore(ptr+32, lo), ret := ptr
        init_ret = real_stmts[0]
        write_hi = real_stmts[1]
        write_lo = real_stmts[2]
        ret_assign = real_stmts[3]

    # init_ret: ret := 0 or ret := <zero-tmp>
    if not isinstance(init_ret, NAssign):
        return False
    if len(init_ret.targets) != 1 or init_ret.targets[0] != ret_id:
        return False
    # Value must be zero or a reference to the zero-init temp variable.
    if len(real_stmts) == 5:
        # 5-stmt form: init_ret must reference the zero-init temp.
        assert isinstance(zero_init, NBind)  # already checked above
        if not (
            isinstance(init_ret.expr, NRef)
            and len(zero_init.targets) == 1
            and init_ret.expr.symbol_id == zero_init.targets[0]
        ):
            return False
    else:
        # 4-stmt form: init_ret must be literal zero.
        if not _is_zero(init_ret.expr):
            return False

    # write_hi: mstore(ptr, hi) as NExprEffect
    if not _is_mstore_effect(write_hi, ptr_id, hi_id):
        return False

    # write_lo: mstore(ptr + 0x20, lo) as NExprEffect
    if not _is_mstore_offset_effect(write_lo, ptr_id, lo_id, 0x20):
        return False

    # ret_assign: ret := ptr
    if not isinstance(ret_assign, NAssign):
        return False
    if len(ret_assign.targets) != 1 or ret_assign.targets[0] != ret_id:
        return False
    if not isinstance(ret_assign.expr, NRef) or ret_assign.expr.symbol_id != ptr_id:
        return False

    return True


def _is_zero(expr: NExpr) -> bool:
    return isinstance(expr, NConst) and expr.value == 0


def _is_mstore_effect(stmt: NStmt, addr_id: SymbolId, value_id: SymbolId) -> bool:
    """Check: NExprEffect(mstore(NRef(addr_id), NRef(value_id)))."""
    if not isinstance(stmt, NExprEffect):
        return False
    call = stmt.expr
    if not isinstance(call, NBuiltinCall):
        return False
    if call.op != "mstore" or len(call.args) != 2:
        return False
    addr, value = call.args
    if not isinstance(addr, NRef) or addr.symbol_id != addr_id:
        return False
    if not isinstance(value, NRef) or value.symbol_id != value_id:
        return False
    return True


def _is_mstore_offset_effect(
    stmt: NStmt, base_id: SymbolId, value_id: SymbolId, offset: int
) -> bool:
    """Check: NExprEffect(mstore(add(base, offset) or add(offset, base), NRef(value_id)))."""
    if not isinstance(stmt, NExprEffect):
        return False
    call = stmt.expr
    if not isinstance(call, NBuiltinCall):
        return False
    if call.op != "mstore" or len(call.args) != 2:
        return False
    addr, value = call.args
    if not isinstance(value, NRef) or value.symbol_id != value_id:
        return False
    return _is_add_offset(addr, base_id, offset)


def _is_add_offset(expr: NExpr, base_id: SymbolId, offset: int) -> bool:
    """Check: add(NRef(base_id), NConst(offset)) or add(NConst(offset), NRef(base_id))."""
    if not isinstance(expr, NBuiltinCall) or expr.op != "add" or len(expr.args) != 2:
        return False
    a, b = expr.args
    if (
        isinstance(a, NRef)
        and a.symbol_id == base_id
        and isinstance(b, NConst)
        and b.value == offset
    ):
        return True
    if (
        isinstance(b, NRef)
        and b.symbol_id == base_id
        and isinstance(a, NConst)
        and a.value == offset
    ):
        return True
    return False


# ---------------------------------------------------------------------------
# Transitive classification (call-graph closure)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class InlineClassification:
    """Inlining decision for a single function."""

    is_pure: bool
    is_deferred: bool
    unsupported_reason: str | None


def classify_helpers(
    summaries: dict[SymbolId, FunctionSummary],
) -> dict[SymbolId, InlineClassification]:
    """Compute transitive inlining classifications from per-function summaries.

    All non-inlineable properties (deferred, unsupported, may_leave,
    calls_top_level) propagate transitively through the call graph.
    """
    # Phase 1: seed from direct properties.
    deferred: set[SymbolId] = set()
    non_pure: set[SymbolId] = set()
    unsupported: dict[SymbolId, str] = {}

    for sid, s in summaries.items():
        if s.writes_memory or s.reads_memory or s.is_uint512_from:
            deferred.add(sid)
            non_pure.add(sid)
        if s.has_for_loop:
            unsupported[sid] = "contains for-loop"
            non_pure.add(sid)
        elif s.has_expr_effects:
            unsupported[sid] = "contains bare expression-statement"
            non_pure.add(sid)
        elif s.calls_unresolved:
            unsupported[sid] = "calls unresolved function"
            non_pure.add(sid)
        elif s.has_effectful_condition:
            unsupported[sid] = "function call in control-flow condition"
            non_pure.add(sid)
        # may_leave does NOT make a helper non-pure — the inliner handles
        # leave via NIte(leave_cond, leave_val, else_val) merge.
        if s.calls_top_level:
            non_pure.add(sid)

    # Phase 2: propagate transitively through the call graph.
    # If A calls B and B is non-pure for any reason, A is also non-pure.
    # If B is deferred, A is also deferred.
    changed = True
    while changed:
        changed = False
        for sid, s in summaries.items():
            if sid not in non_pure and s.called_functions & non_pure:
                non_pure.add(sid)
                changed = True
            if sid not in deferred and s.called_functions & deferred:
                deferred.add(sid)
                changed = True

    # Phase 3: build classifications.
    result: dict[SymbolId, InlineClassification] = {}
    for sid in summaries:
        reason = unsupported.get(sid)
        is_def = sid in deferred
        is_p = sid not in non_pure
        result[sid] = InlineClassification(
            is_pure=is_p,
            is_deferred=is_def,
            unsupported_reason=reason,
        )
    return result


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def classify_function_scope(
    func: NormalizedFunction,
) -> dict[SymbolId, InlineClassification]:
    """Classify all nested helpers in a function for inlining decisions.

    Recursively collects ``NFunctionDef`` nodes from the entire function
    body (including inside if/switch/for blocks), summarizes each, then
    runs transitive classification.
    """
    fdefs: list[NFunctionDef] = []
    _collect_function_defs(func.body, fdefs)
    summaries: dict[SymbolId, FunctionSummary] = {}
    for fdef in fdefs:
        base = summarize_function(fdef.body)
        summaries[fdef.symbol_id] = FunctionSummary(
            writes_memory=base.writes_memory,
            reads_memory=base.reads_memory,
            may_leave=base.may_leave,
            has_for_loop=base.has_for_loop,
            has_expr_effects=base.has_expr_effects,
            has_effectful_condition=base.has_effectful_condition,
            calls_unresolved=base.calls_unresolved,
            calls_top_level=base.calls_top_level,
            called_functions=base.called_functions,
            called_builtins=base.called_builtins,
            is_uint512_from=_is_uint512_from_shape(fdef),
        )
    return classify_helpers(summaries)


def _collect_function_defs(block: NBlock, out: list[NFunctionDef]) -> None:
    """Recursively collect all NFunctionDef nodes from a block tree.

    Descends into control-flow blocks AND into NFunctionDef bodies,
    so deeply-nested helpers (helper inside helper) are found.
    """
    for stmt in block.stmts:
        if isinstance(stmt, NFunctionDef):
            out.append(stmt)
            _collect_function_defs(stmt.body, out)
        elif isinstance(stmt, NIf):
            _collect_function_defs(stmt.then_body, out)
        elif isinstance(stmt, NSwitch):
            for case in stmt.cases:
                _collect_function_defs(case.body, out)
            if stmt.default is not None:
                _collect_function_defs(stmt.default, out)
        elif isinstance(stmt, NFor):
            _collect_function_defs(stmt.init, out)
            _collect_function_defs(stmt.post, out)
            _collect_function_defs(stmt.body, out)
        elif isinstance(stmt, NBlock):
            _collect_function_defs(stmt, out)
