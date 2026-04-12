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
from .norm_optimize_shared import drop_dead_runtime_suffix, sequential_block
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
    for idx, stmt in enumerate(block.stmts):
        if not _append_stmt_sequence(out, _simplify_stmt(stmt)):
            out.extend(drop_dead_runtime_suffix(block.stmts[idx + 1 :]))
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

    if isinstance(stmt, NFor):
        init = _simplify_block(stmt.init)
        if _definitely_terminates(init):
            preamble = sequential_block(init)
            return [preamble] if preamble is not None else []

        condition_setup = (
            _simplify_block(stmt.condition_setup)
            if stmt.condition_setup is not None
            else None
        )
        if condition_setup is not None and _definitely_terminates(condition_setup):
            preamble = sequential_block(init, condition_setup)
            return [preamble] if preamble is not None else []

        cond = fold_expr(stmt.condition)
        if isinstance(cond, NConst) and cond.value == 0:
            preamble = sequential_block(init, condition_setup)
            return [preamble] if preamble is not None else []

        return [
            NFor(
                init=init,
                condition=cond,
                condition_setup=condition_setup,
                post=_simplify_block(stmt.post),
                body=_simplify_block(stmt.body),
            )
        ]

    if isinstance(stmt, NFunctionDef):
        return [_simplify_function_def(stmt)]

    # All other variants: fold expressions + recurse blocks
    return [map_stmt(stmt, map_expr_fn=fold_expr, map_block_fn=_simplify_block)]


def _append_stmt_sequence(out: list[NStmt], stmts: list[NStmt]) -> bool:
    """Append one simplified statement expansion.

    If a runtime statement in *stmts* definitely terminates, preserve only later
    sibling ``NFunctionDef`` nodes from that same expansion.
    """

    for idx, stmt in enumerate(stmts):
        out.append(stmt)
        if _definitely_terminates(stmt):
            out.extend(drop_dead_runtime_suffix(stmts[idx + 1 :]))
            return False
    return True


def _stmt_sequence_definitely_terminates(stmts: tuple[NStmt, ...]) -> bool:
    for stmt in stmts:
        if _definitely_terminates(stmt):
            return True
    return False


def _definitely_terminates(stmt: NStmt) -> bool:
    if isinstance(stmt, NLeave):
        return True
    if isinstance(stmt, NBlock):
        return _stmt_sequence_definitely_terminates(stmt.stmts)
    if isinstance(stmt, NIf):
        return False
    if isinstance(stmt, NSwitch):
        return False
    if isinstance(stmt, NFor):
        return False
    if isinstance(stmt, (NBind, NAssign, NExprEffect, NStore, NFunctionDef)):
        return False
    assert_never(stmt)
