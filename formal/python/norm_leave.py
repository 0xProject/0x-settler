"""
Leave lowering for normalized IR.

This module owns the ``leave`` to ``did_leave`` rewrite shared by
the inliner and the public normalization pipeline.
"""

from __future__ import annotations

from typing import assert_never

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
    NLeave,
    NRef,
    NormalizedFunction,
    NStmt,
    NStore,
    NSwitch,
    NSwitchCase,
)
from .norm_walk import SymbolAllocator, for_each_stmt, max_symbol_id
from .yul_ast import SymbolId


def lower_leave(func: NormalizedFunction) -> NormalizedFunction:
    """Rewrite ``leave`` to ``did_leave`` flag semantics."""
    if not _contains_leave(func.body):
        return func

    alloc = SymbolAllocator(max_symbol_id(func) + 1)
    did_leave_id = alloc.alloc()
    did_leave_name = f"_did_leave_{did_leave_id._id}"
    did_leave_ref = NRef(symbol_id=did_leave_id, name=did_leave_name)

    rewritten = rewrite_leave_as_flag(func.body, did_leave_id)
    out: list[NStmt] = [
        NBind(
            targets=(did_leave_id,),
            target_names=(did_leave_name,),
            expr=NConst(0),
        )
    ]
    out.extend(guard_stmts_after_leave(rewritten.stmts, did_leave_id, did_leave_ref))

    return NormalizedFunction(
        name=func.name,
        params=func.params,
        param_names=func.param_names,
        returns=func.returns,
        return_names=func.return_names,
        body=NBlock(tuple(out)),
    )


def rewrite_leave_as_flag(block: NBlock, did_leave_id: SymbolId) -> NBlock:
    """Rewrite all ``NLeave`` nodes to ``did_leave := 1`` recursively."""
    return NBlock(
        tuple(_rewrite_leave_stmt(stmt, did_leave_id) for stmt in block.stmts)
    )


def guard_stmts_after_leave(
    stmts: tuple[NStmt, ...],
    did_leave_id: SymbolId,
    did_leave_ref: NExpr,
) -> list[NStmt]:
    """Group post-leave statements into maximal guarded blocks."""
    out: list[NStmt] = []
    may_have_left = False
    pending: list[NStmt] = []

    def flush() -> None:
        if pending:
            guard = NBuiltinCall(op="iszero", args=(did_leave_ref,))
            out.append(NIf(condition=guard, then_body=NBlock(tuple(pending))))
            pending.clear()

    for stmt in stmts:
        if may_have_left:
            if _stmt_sets_leave_flag(stmt, did_leave_id):
                flush()
                out.append(stmt)
            else:
                pending.append(stmt)
            continue

        out.append(stmt)
        if _stmt_sets_leave_flag(stmt, did_leave_id):
            may_have_left = True

    flush()
    return out


def _contains_leave(block: NBlock) -> bool:
    found = False

    def visit(stmt: NStmt) -> None:
        nonlocal found
        if isinstance(stmt, NLeave):
            found = True

    for_each_stmt(block, visit)
    return found


def _rewrite_leave_stmt(stmt: NStmt, did_leave_id: SymbolId) -> NStmt:
    if isinstance(stmt, NLeave):
        return NAssign(
            targets=(did_leave_id,),
            target_names=(f"_did_leave_{did_leave_id._id}",),
            expr=NConst(1),
        )
    if isinstance(stmt, NIf):
        return NIf(
            condition=stmt.condition,
            then_body=rewrite_leave_as_flag(stmt.then_body, did_leave_id),
        )
    if isinstance(stmt, NBlock):
        return rewrite_leave_as_flag(stmt, did_leave_id)
    if isinstance(stmt, NSwitch):
        return NSwitch(
            discriminant=stmt.discriminant,
            cases=tuple(
                NSwitchCase(
                    value=case.value,
                    body=rewrite_leave_as_flag(case.body, did_leave_id),
                )
                for case in stmt.cases
            ),
            default=(
                rewrite_leave_as_flag(stmt.default, did_leave_id)
                if stmt.default is not None
                else None
            ),
        )
    if isinstance(stmt, NFor):
        return NFor(
            init=rewrite_leave_as_flag(stmt.init, did_leave_id),
            condition=stmt.condition,
            condition_setup=(
                rewrite_leave_as_flag(stmt.condition_setup, did_leave_id)
                if stmt.condition_setup is not None
                else None
            ),
            post=rewrite_leave_as_flag(stmt.post, did_leave_id),
            body=rewrite_leave_as_flag(stmt.body, did_leave_id),
        )
    if isinstance(stmt, (NBind, NAssign, NExprEffect, NStore, NFunctionDef)):
        return stmt
    assert_never(stmt)


def _stmt_sets_leave_flag(stmt: NStmt, did_leave_id: SymbolId) -> bool:
    found = False

    def visit(sub_stmt: NStmt) -> None:
        nonlocal found
        if isinstance(sub_stmt, NAssign) and did_leave_id in sub_stmt.targets:
            found = True

    if isinstance(stmt, NFunctionDef):
        return False
    for_each_stmt(NBlock((stmt,)), visit)
    return found
