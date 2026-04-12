"""
Leave lowering for normalized IR.

This module owns the canonical ``leave`` to ``did_leave`` lowering
shared by the inliner and the public normalization pipeline.
"""

from __future__ import annotations

from typing import assert_never

from .norm_ir import (
    NAssign,
    NBind,
    NBlock,
    NBuiltinCall,
    NConst,
    NExprEffect,
    NFor,
    NFunctionDef,
    NIf,
    NIte,
    NLeave,
    NormalizedFunction,
    NRef,
    NStmt,
    NStore,
    NSwitch,
    NSwitchCase,
)
from .norm_walk import NBlockItem, SymbolAllocator, for_each_stmt, max_symbol_id
from .yul_ast import SymbolId


def lower_leave(func: NormalizedFunction) -> NormalizedFunction:
    """Rewrite ``leave`` to ``did_leave`` flag semantics."""
    if not _contains_leave(func.body):
        return func

    alloc = SymbolAllocator(max_symbol_id(func) + 1)
    did_leave_id = alloc.alloc()
    did_leave_name = _did_leave_name(did_leave_id)

    lowered_body = lower_leave_block(func.body, did_leave_id)
    out: list[NStmt] = [
        NBind(
            targets=(did_leave_id,),
            target_names=(did_leave_name,),
            expr=NConst(0),
        )
    ]
    out.extend(lowered_body.stmts)

    return NormalizedFunction(
        name=func.name,
        params=func.params,
        param_names=func.param_names,
        returns=func.returns,
        return_names=func.return_names,
        body=NBlock(defs=lowered_body.defs, stmts=tuple(out)),
    )


def lower_leave_block(block: NBlock, did_leave_id: SymbolId) -> NBlock:
    """Lower ``leave`` correctly for one runtime block subtree.

    This is the canonical subtree transformation shared by both the
    top-level normalization pipeline and block inlining.
    """
    return NBlock(
        defs=block.defs,
        stmts=tuple(_lower_leave_stmt_list(block.stmts, did_leave_id)),
    )


def _lower_leave_stmt_list(
    stmts: tuple[NStmt, ...],
    did_leave_id: SymbolId,
) -> list[NStmt]:
    """Lower one statement list, guarding runtime suffixes after ``leave``."""
    out: list[NStmt] = []
    for idx, stmt in enumerate(stmts):
        lowered = _lower_leave_stmt(stmt, did_leave_id)
        out.append(lowered)
        if _stmt_sets_leave_flag(lowered, did_leave_id):
            out.extend(_guard_runtime_suffix(stmts[idx + 1 :], did_leave_id))
            break
    return out


def _contains_leave(block: NBlock) -> bool:
    found = False

    def visit(stmt: NBlockItem) -> None:
        nonlocal found
        if isinstance(stmt, NLeave):
            found = True

    for_each_stmt(block, visit)
    return found


def _lower_leave_stmt(stmt: NStmt, did_leave_id: SymbolId) -> NStmt:
    if isinstance(stmt, NLeave):
        return NAssign(
            targets=(did_leave_id,),
            target_names=(_did_leave_name(did_leave_id),),
            expr=NConst(1),
        )
    if isinstance(stmt, NIf):
        return NIf(
            condition=stmt.condition,
            then_body=lower_leave_block(stmt.then_body, did_leave_id),
        )
    if isinstance(stmt, NBlock):
        return lower_leave_block(stmt, did_leave_id)
    if isinstance(stmt, NSwitch):
        return NSwitch(
            discriminant=stmt.discriminant,
            cases=tuple(
                NSwitchCase(
                    value=case.value,
                    body=lower_leave_block(case.body, did_leave_id),
                )
                for case in stmt.cases
            ),
            default=(
                lower_leave_block(stmt.default, did_leave_id)
                if stmt.default is not None
                else None
            ),
        )
    if isinstance(stmt, NFor):
        lowered_condition_setup = (
            lower_leave_block(stmt.condition_setup, did_leave_id)
            if stmt.condition_setup is not None
            else None
        )
        lowered_post = lower_leave_block(stmt.post, did_leave_id)
        return NFor(
            init=lower_leave_block(stmt.init, did_leave_id),
            condition=NIte(
                cond=_not_did_leave(did_leave_id),
                if_true=stmt.condition,
                if_false=NConst(0),
            ),
            condition_setup=(
                _guard_runtime_block(lowered_condition_setup, did_leave_id)
                if lowered_condition_setup is not None
                else None
            ),
            post=_guard_runtime_block(lowered_post, did_leave_id),
            body=lower_leave_block(stmt.body, did_leave_id),
        )
    if isinstance(stmt, (NBind, NAssign, NExprEffect, NStore)):
        return stmt
    assert_never(stmt)


def _guard_runtime_suffix(
    stmts: tuple[NStmt, ...],
    did_leave_id: SymbolId,
) -> list[NStmt]:
    """Guard the runtime suffix after a statement that executes ``leave``."""
    if not stmts:
        return []
    lowered = _lower_leave_stmt_list(stmts, did_leave_id)
    return [_guard_stmt_block(NBlock(stmts=tuple(lowered)), did_leave_id)]


def _guard_runtime_block(block: NBlock, did_leave_id: SymbolId) -> NBlock:
    if not block.stmts:
        return block
    return NBlock(stmts=(_guard_stmt_block(block, did_leave_id),))


def _guard_stmt_block(block: NBlock, did_leave_id: SymbolId) -> NIf:
    return NIf(condition=_not_did_leave(did_leave_id), then_body=block)


def _did_leave_name(did_leave_id: SymbolId) -> str:
    return f"_did_leave_{did_leave_id._id}"


def _not_did_leave(did_leave_id: SymbolId) -> NBuiltinCall:
    return NBuiltinCall(
        op="iszero",
        args=(NRef(symbol_id=did_leave_id, name=_did_leave_name(did_leave_id)),),
    )


def _stmt_sets_leave_flag(stmt: NStmt, did_leave_id: SymbolId) -> bool:
    found = False

    def visit(sub_stmt: NBlockItem) -> None:
        nonlocal found
        if isinstance(sub_stmt, NAssign) and did_leave_id in sub_stmt.targets:
            found = True

    for_each_stmt(NBlock(stmts=(stmt,)), visit)
    return found
