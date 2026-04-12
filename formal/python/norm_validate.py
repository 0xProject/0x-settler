"""Validate the post-memory normalized IR accepted by restricted lowering."""

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
from .yul_ast import ValidationError


def validate_restricted_boundary(
    func: NormalizedFunction,
    *,
    allowed_model_calls: frozenset[str],
) -> None:
    """Reject residual live constructs unsupported by restricted lowering."""
    if not func.returns:
        raise ValidationError(f"Selected function {func.name!r} has zero return values")
    _validate_block(
        func.body,
        allowed_model_calls=allowed_model_calls,
        context=f"selected target {func.name!r}",
    )


def _validate_block(
    block: NBlock,
    *,
    allowed_model_calls: frozenset[str],
    context: str,
) -> None:
    for stmt in block.stmts:
        _validate_stmt(
            stmt,
            allowed_model_calls=allowed_model_calls,
            context=context,
        )


def _validate_stmt(
    stmt: NStmt,
    *,
    allowed_model_calls: frozenset[str],
    context: str,
) -> None:
    if isinstance(stmt, NBind):
        if stmt.expr is not None:
            _validate_expr(
                stmt.expr,
                allowed_model_calls=allowed_model_calls,
                context=context,
            )
        return

    if isinstance(stmt, NAssign):
        _validate_expr(
            stmt.expr,
            allowed_model_calls=allowed_model_calls,
            context=context,
        )
        return

    if isinstance(stmt, NExprEffect):
        raise ValidationError(
            f"{context} contains unsupported expression-statement "
            f"{type(stmt.expr).__name__}. Refuse to proceed with incomplete semantics."
        )

    if isinstance(stmt, NIf):
        _validate_expr(
            stmt.condition,
            allowed_model_calls=allowed_model_calls,
            context=context,
        )
        _validate_block(
            stmt.then_body,
            allowed_model_calls=allowed_model_calls,
            context=context,
        )
        return

    if isinstance(stmt, NSwitch):
        _validate_expr(
            stmt.discriminant,
            allowed_model_calls=allowed_model_calls,
            context=context,
        )
        for case in stmt.cases:
            _validate_block(
                case.body,
                allowed_model_calls=allowed_model_calls,
                context=context,
            )
        if stmt.default is not None:
            _validate_block(
                stmt.default,
                allowed_model_calls=allowed_model_calls,
                context=context,
            )
        return

    if isinstance(stmt, NFor):
        raise ValidationError(
            f"{context} contains unsupported for-loop after simplification"
        )

    if isinstance(stmt, NLeave):
        raise ValidationError(
            "NLeave in restricted IR lowering — should have been inlined"
        )

    if isinstance(stmt, NBlock):
        _validate_block(
            stmt,
            allowed_model_calls=allowed_model_calls,
            context=context,
        )
        return

    assert_never(stmt)


def _validate_expr(
    expr: NExpr,
    *,
    allowed_model_calls: frozenset[str],
    context: str,
) -> None:
    if isinstance(expr, (NConst, NRef)):
        return

    if isinstance(expr, NBuiltinCall):
        if expr.op in {"mload", "mstore", "mstore8"}:
            raise ValidationError(
                f"{context} reaches restricted IR lowering with residual memory "
                f"builtin {expr.op!r}. Memory must be lowered before this stage."
            )
        for arg in expr.args:
            _validate_expr(
                arg,
                allowed_model_calls=allowed_model_calls,
                context=context,
            )
        return

    if isinstance(expr, NLocalCall):
        raise ValidationError(
            f"{context} reaches restricted IR lowering with residual local helper "
            f"call {expr.name!r}. "
            f"All non-selected helpers must be inlined before restricted lowering."
        )

    if isinstance(expr, NTopLevelCall):
        if expr.name not in allowed_model_calls:
            raise ValidationError(
                f"{context} reaches restricted IR lowering with non-selected "
                f"model call {expr.name!r}. "
                f"Only explicitly selected targets may remain as model calls."
            )
        for arg in expr.args:
            _validate_expr(
                arg,
                allowed_model_calls=allowed_model_calls,
                context=context,
            )
        return

    if isinstance(expr, NUnresolvedCall):
        raise ValidationError(
            f"Unresolved call to {expr.name!r} in {context}; unresolved call is live"
        )

    if isinstance(expr, NIte):
        _validate_expr(
            expr.cond,
            allowed_model_calls=allowed_model_calls,
            context=context,
        )
        _validate_expr(
            expr.if_true,
            allowed_model_calls=allowed_model_calls,
            context=context,
        )
        _validate_expr(
            expr.if_false,
            allowed_model_calls=allowed_model_calls,
            context=context,
        )
        return

    assert_never(expr)
