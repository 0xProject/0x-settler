"""
Shared optimizer helpers for normalized-IR passes.
"""

from __future__ import annotations

from collections.abc import Callable, Iterable

from .norm_ir import NBlock, NConst, NExpr, NFunctionDef, NIte, NStmt


def rewrite_runtime_suffix_preserving_hoisted_defs(
    stmts: Iterable[NStmt],
    rewrite_runtime: Callable[[tuple[NStmt, ...]], Iterable[NStmt]],
) -> list[NStmt]:
    """Rewrite runtime chunks while preserving current-block hoisted defs.

    Yul local function declarations are hoisted within their enclosing block, so
    suffix rewrites must preserve sibling ``NFunctionDef`` nodes even when later
    runtime statements become unreachable or need restructuring.
    """

    out: list[NStmt] = []
    pending_runtime: list[NStmt] = []

    def flush() -> None:
        if not pending_runtime:
            return
        out.extend(rewrite_runtime(tuple(pending_runtime)))
        pending_runtime.clear()

    for stmt in stmts:
        if isinstance(stmt, NFunctionDef):
            flush()
            out.append(stmt)
            continue
        pending_runtime.append(stmt)

    flush()
    return out


def drop_dead_runtime_suffix(stmts: Iterable[NStmt]) -> list[NStmt]:
    """Discard runtime suffix statements while preserving hoisted defs."""

    return rewrite_runtime_suffix_preserving_hoisted_defs(stmts, lambda _chunk: ())


def simplify_ite(cond: NExpr, if_true: NExpr, if_false: NExpr) -> NExpr:
    """Fold an ``NIte`` when the condition or branches make it redundant."""

    if if_true == if_false:
        return if_true
    if isinstance(cond, NConst):
        return if_true if cond.value != 0 else if_false
    return NIte(cond=cond, if_true=if_true, if_false=if_false)


def sequential_block(*blocks: NBlock | None) -> NBlock | None:
    """Build one executable block from sequential sub-blocks.

    Each non-empty input block is preserved as its own nested ``NBlock`` so
    block-local helper hoisting does not leak across former block boundaries.
    """

    executed = tuple(block for block in blocks if block is not None and block.stmts)
    if not executed:
        return None
    return NBlock(executed)
