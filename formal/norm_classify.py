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

import enum
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
    NStore,
    NSwitch,
    NTopLevelCall,
    NUnresolvedCall,
)
from norm_walk import collect_function_defs, for_each_expr
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
            _walk_expr_effects(acc, stmt.expr)
    elif isinstance(stmt, NAssign):
        _walk_expr_effects(acc, stmt.expr)
    elif isinstance(stmt, NExprEffect):
        if not _is_known_effect_call(stmt.expr):
            acc.has_expr_effects = True
        _walk_expr_effects(acc, stmt.expr)
    elif isinstance(stmt, NStore):
        acc.writes_memory = True
        _walk_expr_effects(acc, stmt.addr)
        _walk_expr_effects(acc, stmt.value)
    elif isinstance(stmt, NIf):
        if _has_call_in_expr(stmt.condition):
            acc.has_effectful_condition = True
        _walk_expr_effects(acc, stmt.condition)
        _walk_block(acc, stmt.then_body)
    elif isinstance(stmt, NSwitch):
        if _has_call_in_expr(stmt.discriminant):
            acc.has_effectful_condition = True
        _walk_expr_effects(acc, stmt.discriminant)
        for case in stmt.cases:
            _walk_block(acc, case.body)
        if stmt.default is not None:
            _walk_block(acc, stmt.default)
    elif isinstance(stmt, NFor):
        acc.has_for_loop = True
        if _has_call_in_expr(stmt.condition):
            acc.has_effectful_condition = True
        _walk_block(acc, stmt.init)
        _walk_expr_effects(acc, stmt.condition)
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
    else:
        assert_never(stmt)


def _walk_expr_effects(acc: _SummaryAccumulator, expr: NExpr) -> None:
    """Walk an expression and accumulate effects using for_each_expr."""

    def visit(e: NExpr) -> None:
        if isinstance(e, NBuiltinCall):
            acc.called_builtins.add(e.op)
            if e.op in _MEMORY_WRITE_OPS:
                acc.writes_memory = True
            if e.op in _MEMORY_READ_OPS:
                acc.reads_memory = True
        elif isinstance(e, NLocalCall):
            acc.called_functions.add(e.symbol_id)
        elif isinstance(e, NTopLevelCall):
            acc.calls_top_level = True
        elif isinstance(e, NUnresolvedCall):
            acc.calls_unresolved = True

    for_each_expr(expr, visit)


def _has_call_in_expr(expr: NExpr) -> bool:
    """Check if an expression contains any function call."""
    found: list[bool] = [False]

    def visit(e: NExpr) -> None:
        if isinstance(e, (NLocalCall, NTopLevelCall, NUnresolvedCall)):
            found[0] = True

    for_each_expr(expr, visit)
    return found[0]


def _is_known_effect_call(expr: NExpr) -> bool:
    """Check if an expression-statement is a known effect pattern."""
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
    real_stmts: list[NStmt] = [s for s in stmts if not isinstance(s, NFunctionDef)]

    if len(real_stmts) not in (4, 5):
        return False

    ptr_id = fdef.params[0]
    hi_id = fdef.params[1]
    lo_id = fdef.params[2]
    ret_id = fdef.returns[0]

    if len(real_stmts) == 5:
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
        init_ret = real_stmts[0]
        write_hi = real_stmts[1]
        write_lo = real_stmts[2]
        ret_assign = real_stmts[3]

    if not isinstance(init_ret, NAssign):
        return False
    if len(init_ret.targets) != 1 or init_ret.targets[0] != ret_id:
        return False
    if len(real_stmts) == 5:
        assert isinstance(zero_init, NBind)
        if not (
            isinstance(init_ret.expr, NRef)
            and len(zero_init.targets) == 1
            and init_ret.expr.symbol_id == zero_init.targets[0]
        ):
            return False
    else:
        if not _is_zero(init_ret.expr):
            return False

    if not _is_mstore_effect(write_hi, ptr_id, hi_id):
        return False
    if not _is_mstore_offset_effect(write_lo, ptr_id, lo_id, 0x20):
        return False

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


class InlineStrategy(enum.Enum):
    """How a helper should be inlined."""

    EXPR_INLINE = "expr_inline"
    """Pure helper: inline body as symbolic expression substitution."""

    BLOCK_INLINE = "block_inline"
    """Leave-bearing helper: clone body into caller with did_leave flag."""

    EFFECT_LOWER = "effect_lower"
    """uint512.from shape: emit explicit NStore statements at call site."""

    DO_NOT_INLINE = "do_not_inline"
    """Cannot be inlined: unsupported, top-level calls, etc."""


@dataclass(frozen=True)
class InlineClassification:
    """Inlining decision for a single function."""

    strategy: InlineStrategy
    is_pure: bool
    is_deferred: bool
    unsupported_reason: str | None


def classify_helpers(
    summaries: dict[SymbolId, FunctionSummary],
) -> dict[SymbolId, InlineClassification]:
    """Compute transitive inlining classifications from per-function summaries.

    All non-inlineable properties (deferred, unsupported, calls_top_level)
    propagate transitively through the call graph.
    may_leave does NOT make a helper non-pure — the inliner handles
    leave via NIte(leave_cond, leave_val, else_val) merge.
    """
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
        if s.calls_top_level:
            non_pure.add(sid)

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

    result: dict[SymbolId, InlineClassification] = {}
    for sid, s in summaries.items():
        reason = unsupported.get(sid)
        is_def = sid in deferred
        is_p = sid not in non_pure

        # Determine strategy.
        if reason is not None or s.calls_top_level:
            strategy = InlineStrategy.DO_NOT_INLINE
        elif s.is_uint512_from:
            strategy = InlineStrategy.EFFECT_LOWER
        elif is_def:
            strategy = InlineStrategy.DO_NOT_INLINE
        elif s.may_leave:
            strategy = InlineStrategy.BLOCK_INLINE
        elif is_p:
            strategy = InlineStrategy.EXPR_INLINE
        else:
            strategy = InlineStrategy.DO_NOT_INLINE

        result[sid] = InlineClassification(
            strategy=strategy,
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
    fdefs = collect_function_defs(func.body)
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
