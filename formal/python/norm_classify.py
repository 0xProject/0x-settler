"""
Per-function effect analysis and inlining classification for normalized IR.

Walks a ``NormalizedFunction`` to determine each nested helper's effects
(memory, leave, for-loops, expression-statements) and classifies them
for inlining: pure (safe to expression-substitute), deferred (has
memory effects), or unsupported.
"""

from __future__ import annotations

import enum
from dataclasses import dataclass
from typing import assert_never

from .norm_ir import (
    NBlock,
    NBuiltinCall,
    NExpr,
    NExprEffect,
    NFor,
    NFunctionDef,
    NIf,
    NLeave,
    NLocalCall,
    NormalizedFunction,
    NStmt,
    NSwitch,
    NTopLevelCall,
    NUnresolvedCall,
)
from .norm_walk import (
    NBlockItem,
    collect_function_defs,
    expr_contains,
    for_each_expr,
    for_each_stmt,
    for_each_stmt_expr,
)
from .yul_ast import SymbolId

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


def summarize_function(
    body: NBlock,
    *,
    top_level_inline_sids: dict[str, SymbolId] | None = None,
    allowed_model_calls: frozenset[str] = frozenset(),
) -> FunctionSummary:
    """Analyze a function body for effects (non-recursive into nested defs)."""
    acc = _SummaryAccumulator(
        top_level_inline_sids=top_level_inline_sids,
        allowed_model_calls=allowed_model_calls,
    )

    def visit(item: NBlockItem) -> None:
        if isinstance(item, NFunctionDef):
            return
        if isinstance(item, NExprEffect):
            if not _is_recognized_expr_stmt(item.expr):
                acc.has_expr_effects = True
        elif isinstance(item, NIf):
            if _has_call_in_expr(item.condition):
                acc.has_effectful_condition = True
        elif isinstance(item, NSwitch):
            if _has_call_in_expr(item.discriminant):
                acc.has_effectful_condition = True
        elif isinstance(item, NFor):
            acc.has_for_loop = True
            if _has_call_in_expr(item.condition):
                acc.has_effectful_condition = True
        elif isinstance(item, NLeave):
            acc.may_leave = True
        for_each_stmt_expr(item, lambda expr: _walk_expr_effects(acc, expr))

    for_each_stmt(body, visit)
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
    )


class _SummaryAccumulator:
    """Mutable accumulator for the summary walk."""

    def __init__(
        self,
        *,
        top_level_inline_sids: dict[str, SymbolId] | None,
        allowed_model_calls: frozenset[str],
    ) -> None:
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
        self.top_level_inline_sids = (
            dict(top_level_inline_sids) if top_level_inline_sids is not None else {}
        )
        self.allowed_model_calls = allowed_model_calls


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
            inline_sid = acc.top_level_inline_sids.get(e.name)
            if inline_sid is not None:
                acc.called_functions.add(inline_sid)
            elif e.name not in acc.allowed_model_calls:
                acc.calls_top_level = True
        elif isinstance(e, NUnresolvedCall):
            acc.calls_unresolved = True

    for_each_expr(expr, visit)


def _has_call_in_expr(expr: NExpr) -> bool:
    """Check if an expression contains any function call."""
    return expr_contains(
        expr,
        lambda e: isinstance(e, (NLocalCall, NTopLevelCall, NUnresolvedCall)),
    )


def _is_recognized_expr_stmt(expr: NExpr) -> bool:
    """Check if an expression-statement is a recognized pattern.

    Memory writes and resolved helper/model calls are expected as bare
    statements. Anything else (e.g. a bare ``add(x, y)`` or unresolved call)
    is unusual and flags ``has_expr_effects``.
    """
    if isinstance(expr, NBuiltinCall):
        return expr.op in _MEMORY_WRITE_OPS
    return isinstance(expr, (NLocalCall, NTopLevelCall))


# ---------------------------------------------------------------------------
# Transitive classification (call-graph closure)
# ---------------------------------------------------------------------------


class InlineStrategy(enum.Enum):
    """How a helper should be inlined."""

    EXPR_INLINE = "expr_inline"
    """Pure helper: inline body as symbolic expression substitution."""

    BLOCK_INLINE = "block_inline"
    """Leave-bearing helper: clone body into caller with did_leave flag."""

    DO_NOT_INLINE = "do_not_inline"
    """Cannot be inlined: unsupported, top-level calls, etc."""


class UnsupportedKind(enum.Enum):
    """Intrinsic blockers that prevent helper inlining."""

    FOR_LOOP = "for_loop"
    BARE_EXPR_STMT = "bare_expr_stmt"
    UNRESOLVED_CALL = "unresolved_call"
    EFFECTFUL_CONDITION = "effectful_condition"
    TOP_LEVEL_CALL = "top_level_call"


def unsupported_kind_reason(kind: UnsupportedKind) -> str:
    """Render the stable human-readable reason for an unsupported helper."""
    if kind == UnsupportedKind.FOR_LOOP:
        return "contains for-loop"
    if kind == UnsupportedKind.BARE_EXPR_STMT:
        return "contains bare expression-statement"
    if kind == UnsupportedKind.UNRESOLVED_CALL:
        return "calls unresolved function"
    if kind == UnsupportedKind.EFFECTFUL_CONDITION:
        return "function call in control-flow condition"
    if kind == UnsupportedKind.TOP_LEVEL_CALL:
        return "calls non-model top-level helper"
    assert_never(kind)


def first_unsupported_kind(summary: FunctionSummary) -> UnsupportedKind | None:
    """Return the first structural blocker for helper inlining."""
    if summary.has_for_loop:
        return UnsupportedKind.FOR_LOOP
    if summary.has_expr_effects:
        return UnsupportedKind.BARE_EXPR_STMT
    if summary.calls_unresolved:
        return UnsupportedKind.UNRESOLVED_CALL
    if summary.has_effectful_condition:
        return UnsupportedKind.EFFECTFUL_CONDITION
    if summary.calls_top_level:
        return UnsupportedKind.TOP_LEVEL_CALL
    return None


@dataclass(frozen=True)
class InlineClassification:
    """Inlining decision for a single function."""

    strategy: InlineStrategy
    is_pure: bool
    is_deferred: bool
    unsupported_kind: UnsupportedKind | None

    @property
    def unsupported_reason(self) -> str | None:
        return (
            unsupported_kind_reason(self.unsupported_kind)
            if self.unsupported_kind is not None
            else None
        )


def classify_helpers(
    summaries: dict[SymbolId, FunctionSummary],
) -> dict[SymbolId, InlineClassification]:
    """Compute transitive inlining classifications from per-function summaries.

    Deferred helpers (memory readers/writers) remain non-pure, but they
    are still structurally inlineable so later memory lowering can
    eliminate their effects in the selected target.

    Unsupported helpers remain ``DO_NOT_INLINE`` until dead-code
    elimination proves them unreachable.
    """
    deferred: set[SymbolId] = set()
    non_pure: set[SymbolId] = set()
    unsupported: dict[SymbolId, UnsupportedKind] = {}

    for sid, s in summaries.items():
        if s.writes_memory or s.reads_memory:
            deferred.add(sid)
            non_pure.add(sid)
        blocker = first_unsupported_kind(s)
        if blocker is not None:
            unsupported[sid] = blocker
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
        unsupported_kind = unsupported.get(sid)
        is_def = sid in deferred
        is_p = sid not in non_pure

        # Determine strategy.
        #
        # The classifier is strict: unsupported constructs remain
        # unsupported here. Dead-code elimination belongs in the
        # simplifier, and fail-closed acceptance belongs in the
        # validation pass before restricted lowering.
        if unsupported_kind is not None:
            strategy = InlineStrategy.DO_NOT_INLINE
        elif is_def or s.may_leave:
            strategy = InlineStrategy.BLOCK_INLINE
        elif not is_p:
            strategy = InlineStrategy.DO_NOT_INLINE
        else:
            strategy = InlineStrategy.EXPR_INLINE

        result[sid] = InlineClassification(
            strategy=strategy,
            is_pure=is_p,
            is_deferred=is_def,
            unsupported_kind=unsupported_kind,
        )
    return result


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def classify_function_scope(
    func: NormalizedFunction,
    *,
    top_level_inline_sids: dict[str, SymbolId] | None = None,
    allowed_model_calls: frozenset[str] = frozenset(),
) -> dict[SymbolId, InlineClassification]:
    """Classify all nested helpers in a function for inlining decisions.

    Recursively collects ``NFunctionDef`` nodes from the entire function
    body (including inside if/switch/for blocks), summarizes each, then
    runs transitive classification.
    """
    fdefs = collect_function_defs(func.body)
    summaries: dict[SymbolId, FunctionSummary] = {}
    for fdef in fdefs:
        summaries[fdef.symbol_id] = summarize_function(
            fdef.body,
            top_level_inline_sids=top_level_inline_sids,
            allowed_model_calls=allowed_model_calls,
        )
    return classify_helpers(summaries)
