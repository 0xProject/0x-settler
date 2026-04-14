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
    NFunctionDef,
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
from .norm_walk import (
    NBlockItem,
    collect_function_defs,
    first_runtime_local_call,
    for_each_stmt,
    for_each_stmt_expr,
)
from .yul_ast import ValidationError


def restricted_lowering_precondition_error(func: NormalizedFunction) -> str | None:
    """Return the shared precondition failure before restricted lowering."""

    if not func.returns:
        return f"Selected function {func.name!r} has zero return values"
    if collect_function_defs(func.body):
        return (
            f"Nested helper definitions reached restricted lowering for "
            f"selected target {func.name!r}. Seal the helper boundary "
            "before restricted lowering."
        )
    residual_call = first_runtime_local_call(func.body)
    if residual_call is not None:
        return (
            f"Residual local helper call {residual_call.name!r} reached "
            f"restricted lowering for selected target {func.name!r}. "
            "Seal the helper boundary before restricted lowering."
        )
    return None


def validate_restricted_boundary(
    func: NormalizedFunction,
    *,
    allowed_model_calls: frozenset[str],
) -> None:
    """Reject residual live constructs unsupported by restricted lowering."""
    error = restricted_lowering_precondition_error(func)
    if error is not None:
        raise ValidationError(error)
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
    def visit(item: NBlockItem) -> None:
        if isinstance(item, NFunctionDef):
            return
        if isinstance(item, NExprEffect):
            raise ValidationError(
                f"{context} contains unsupported expression-statement "
                f"{type(item.expr).__name__}. Refuse to proceed with incomplete semantics."
            )
        if isinstance(item, NFor):
            raise ValidationError(
                f"{context} contains unsupported for-loop after simplification"
            )
        if isinstance(item, NLeave):
            raise ValidationError(
                "NLeave in restricted IR lowering — should have been lowered"
            )
        for_each_stmt_expr(
            item,
            lambda expr: _validate_expr(
                expr,
                allowed_model_calls=allowed_model_calls,
                context=context,
            ),
        )

    for_each_stmt(block, visit)


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
