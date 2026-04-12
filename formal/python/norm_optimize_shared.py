"""
Shared optimizer helpers for normalized-IR passes.
"""

from __future__ import annotations

from .norm_ir import NBlock, NConst, NExpr, NIte


def const_value(expr: NExpr) -> int | None:
    return expr.value if isinstance(expr, NConst) else None


def const_truthy(expr: NExpr) -> bool | None:
    value = const_value(expr)
    return None if value is None else value != 0


def simplify_ite(cond: NExpr, if_true: NExpr, if_false: NExpr) -> NExpr:
    """Fold an ``NIte`` when the condition or branches make it redundant."""

    if if_true == if_false:
        return if_true
    truthy = const_truthy(cond)
    if truthy is not None:
        return if_true if truthy else if_false
    return NIte(cond=cond, if_true=if_true, if_false=if_false)


def sequential_block(*blocks: NBlock | None) -> NBlock | None:
    """Build one executable block from sequential sub-blocks.

    Each non-empty input block is preserved as its own nested ``NBlock`` so
    block-local helper hoisting does not leak across former block boundaries.
    """

    executed = tuple(
        block for block in blocks if block is not None and (block.defs or block.stmts)
    )
    if not executed:
        return None
    return NBlock(stmts=executed)
