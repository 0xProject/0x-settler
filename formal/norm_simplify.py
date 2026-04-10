"""
General normalized-IR simplification passes.

This pass is intentionally provenance-independent: it applies the same
cleanup to selected targets, local helpers, and top-level helper bodies.
"""

from __future__ import annotations

from evm_builtins import WORD_MOD
from norm_constprop import fold_expr
from norm_ir import (
    NAssign,
    NBind,
    NBlock,
    NBuiltinCall,
    NConst,
    NExprEffect,
    NFor,
    NFunctionDef,
    NIf,
    NLeave,
    NormalizedFunction,
    NRef,
    NStmt,
    NStore,
    NSwitch,
    NSwitchCase,
)


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


def simplify_function_def(fdef: NFunctionDef) -> NFunctionDef:
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
    if isinstance(stmt, NBind):
        return [
            NBind(
                targets=stmt.targets,
                target_names=stmt.target_names,
                expr=fold_expr(stmt.expr) if stmt.expr is not None else None,
            )
        ]

    if isinstance(stmt, NAssign):
        return [
            NAssign(
                targets=stmt.targets,
                target_names=stmt.target_names,
                expr=fold_expr(stmt.expr),
            )
        ]

    if isinstance(stmt, NExprEffect):
        return [NExprEffect(expr=fold_expr(stmt.expr))]

    if isinstance(stmt, NStore):
        return [NStore(addr=fold_expr(stmt.addr), value=fold_expr(stmt.value))]

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
                if case.value.value % WORD_MOD == disc.value:
                    return list(case.body.stmts)
            return list(default.stmts) if default is not None else []
        return [NSwitch(discriminant=disc, cases=cases, default=default)]

    if isinstance(stmt, NFor):
        condition_setup = (
            _simplify_block(stmt.condition_setup)
            if stmt.condition_setup is not None
            else None
        )
        return [
            NFor(
                init=_simplify_block(stmt.init),
                condition=fold_expr(stmt.condition),
                condition_setup=condition_setup,
                post=_simplify_block(stmt.post),
                body=_simplify_block(stmt.body),
            )
        ]

    if isinstance(stmt, NFunctionDef):
        return [simplify_function_def(stmt)]

    if isinstance(stmt, NBlock):
        return [_simplify_block(stmt)]

    if isinstance(stmt, NLeave):
        return [stmt]

    raise TypeError(f"Unexpected normalized statement {type(stmt).__name__}")


def _contains_leave(block: NBlock) -> bool:
    """Check if any NLeave exists in *block* (recursive)."""
    for stmt in block.stmts:
        if isinstance(stmt, NLeave):
            return True
        if isinstance(stmt, NIf) and _contains_leave(stmt.then_body):
            return True
        if isinstance(stmt, NSwitch):
            for case in stmt.cases:
                if _contains_leave(case.body):
                    return True
            if stmt.default is not None and _contains_leave(stmt.default):
                return True
        if isinstance(stmt, NFor):
            if _contains_leave(stmt.body):
                return True
        if isinstance(stmt, NBlock) and _contains_leave(stmt):
            return True
    return False


def lower_leave(func: NormalizedFunction) -> NormalizedFunction:
    """Rewrite ``leave`` to ``did_leave`` flag semantics.

    If the function body contains no ``NLeave``, returns unchanged.
    Otherwise, introduces a ``did_leave`` flag variable, replaces all
    ``NLeave`` with ``did_leave := 1``, and guards subsequent top-level
    statements with ``if iszero(did_leave)``.
    """
    if not _contains_leave(func.body):
        return func

    from norm_inline import SymbolAllocator
    from norm_walk import max_symbol_id

    alloc = SymbolAllocator(max_symbol_id(func) + 1)
    did_leave_id = alloc.alloc()
    did_leave_ref = NRef(symbol_id=did_leave_id, name=f"_did_leave_{did_leave_id._id}")

    # Import leave-rewriting helpers from the inliner.
    from norm_inline import _partition_guarded_stmts, _rewrite_leave_recursive

    rewritten = _rewrite_leave_recursive(func.body, did_leave_id)

    # Prepend did_leave := 0, then group guarded statements.
    out: list[NStmt] = [
        NBind(
            targets=(did_leave_id,),
            target_names=(f"_did_leave_{did_leave_id._id}",),
            expr=NConst(0),
        )
    ]
    out.extend(_partition_guarded_stmts(rewritten.stmts, did_leave_id, did_leave_ref))

    return NormalizedFunction(
        name=func.name,
        params=func.params,
        param_names=func.param_names,
        returns=func.returns,
        return_names=func.return_names,
        body=NBlock(tuple(out)),
    )


def _definitely_terminates(stmt: NStmt) -> bool:
    if isinstance(stmt, NLeave):
        return True
    if isinstance(stmt, NBlock) and stmt.stmts:
        return _definitely_terminates(stmt.stmts[-1])
    if isinstance(stmt, NIf):
        return False
    if isinstance(stmt, NSwitch):
        return False
    if isinstance(stmt, NFor):
        return False
    if isinstance(stmt, (NBind, NAssign, NExprEffect, NStore, NFunctionDef)):
        return False
    raise TypeError(f"Unexpected normalized statement {type(stmt).__name__}")
