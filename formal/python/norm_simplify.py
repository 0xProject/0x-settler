"""
General normalized-IR simplification passes.

This pass is intentionally provenance-independent: it applies the same
cleanup to selected targets, local helpers, and top-level helper bodies.
"""

from __future__ import annotations

from typing import assert_never

from .norm_constprop import fold_expr
from .norm_ir import (
    NAssign,
    NBind,
    NBlock,
    NConst,
    NExprEffect,
    NFor,
    NFunctionDef,
    NIf,
    NLeave,
    NormalizedFunction,
    NStmt,
    NStore,
    NSwitch,
    NSwitchCase,
)
from .norm_walk import map_stmt


def simplify_normalized(func: NormalizedFunction) -> NormalizedFunction:
    """Apply generic control-flow cleanup to a normalized function tree."""
    return NormalizedFunction(
        name=func.name,
        params=func.params,
        param_names=func.param_names,
        returns=func.returns,
        return_names=func.return_names,
        body=_simplify_block(func.body),
    )


def _simplify_function_def(fdef: NFunctionDef) -> NFunctionDef:
    """Apply the same cleanup to a helper definition."""
    return NFunctionDef(
        name=fdef.name,
        symbol_id=fdef.symbol_id,
        params=fdef.params,
        param_names=fdef.param_names,
        returns=fdef.returns,
        return_names=fdef.return_names,
        body=_simplify_block(fdef.body),
    )


def _simplify_block(block: NBlock) -> NBlock:
    out: list[NStmt] = []
    terminated = False
    for stmt in block.stmts:
        if terminated:
            break
        for simplified in _simplify_stmt(stmt):
            out.append(simplified)
            if _definitely_terminates(simplified):
                terminated = True
                break
    return NBlock(tuple(out))


def _simplify_stmt(stmt: NStmt) -> list[NStmt]:
    if isinstance(stmt, NIf):
        cond = fold_expr(stmt.condition)
        then_body = _simplify_block(stmt.then_body)
        if isinstance(cond, NConst):
            return list(then_body.stmts) if cond.value != 0 else []
        return [NIf(condition=cond, then_body=then_body)]

    if isinstance(stmt, NSwitch):
        disc = fold_expr(stmt.discriminant)
        cases = tuple(
            NSwitchCase(value=case.value, body=_simplify_block(case.body))
            for case in stmt.cases
        )
        default = _simplify_block(stmt.default) if stmt.default is not None else None
        if isinstance(disc, NConst):
            for case in cases:
                if case.value.value == disc.value:
                    return list(case.body.stmts)
            return list(default.stmts) if default is not None else []
        return [NSwitch(discriminant=disc, cases=cases, default=default)]

    if isinstance(stmt, NFunctionDef):
        return [_simplify_function_def(stmt)]

    # All other variants: fold expressions + recurse blocks
    return [map_stmt(stmt, map_expr_fn=fold_expr, map_block_fn=_simplify_block)]


def _definitely_terminates(stmt: NStmt) -> bool:
    if isinstance(stmt, NLeave):
        return True
    if isinstance(stmt, NBlock):
        return bool(stmt.stmts) and _definitely_terminates(stmt.stmts[-1])
    if isinstance(stmt, NIf):
        return False
    if isinstance(stmt, NSwitch):
        return False
    if isinstance(stmt, NFor):
        return False
    if isinstance(stmt, (NBind, NAssign, NExprEffect, NStore, NFunctionDef)):
        return False
    assert_never(stmt)
