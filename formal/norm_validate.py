"""
Pre-restricted validation for normalized IR.

This pass defines the public acceptance boundary for the staged path.
It runs after inlining + simplification and before restricted lowering,
so low-level lowering errors do not become the user-facing contract.
"""

from __future__ import annotations

from typing import assert_never

from norm_ir import (
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
    NStore,
    NSwitch,
    NTopLevelCall,
    NUnresolvedCall,
)
from yul_ast import ParseError

_ALLOWED_EXPR_STMT_BUILTINS = frozenset({"mstore", "mstore8"})


def validate_restricted_boundary(
    func: NormalizedFunction,
    *,
    allowed_model_calls: frozenset[str],
    allow_memory_ops: bool = False,
) -> None:
    """Reject residual live constructs unsupported by restricted lowering."""
    _validate_public_function_contract(func)
    _validate_block(
        func.body,
        allowed_model_calls=allowed_model_calls,
        allow_memory_ops=allow_memory_ops,
        context=f"selected target {func.name!r}",
        inside_control_flow=False,
    )


def _validate_public_function_contract(func: NormalizedFunction) -> None:
    """Validate the public selected-target contract before lowering."""
    if not func.returns:
        raise ParseError(f"Selected function {func.name!r} has zero return values")

    from restricted_names import legalize_identifier_base
    from yul_to_lean import validate_ident

    for raw in func.param_names:
        base = legalize_identifier_base(raw, avoid_reserved=False)
        validate_ident(base, what=f"selected param name in {func.name!r}")
    for raw in func.return_names:
        base = legalize_identifier_base(raw, avoid_reserved=False)
        validate_ident(base, what=f"selected return name in {func.name!r}")


def _validate_block(
    block: NBlock,
    *,
    allowed_model_calls: frozenset[str],
    allow_memory_ops: bool,
    context: str,
    inside_control_flow: bool,
) -> None:
    for stmt in block.stmts:
        _validate_stmt(
            stmt,
            allowed_model_calls=allowed_model_calls,
            allow_memory_ops=allow_memory_ops,
            context=context,
            inside_control_flow=inside_control_flow,
        )


def _validate_stmt(
    stmt,
    *,
    allowed_model_calls: frozenset[str],
    allow_memory_ops: bool,
    context: str,
    inside_control_flow: bool,
) -> None:
    if isinstance(stmt, NBind):
        if stmt.expr is not None:
            _validate_expr(
                stmt.expr,
                allowed_model_calls=allowed_model_calls,
                allow_memory_ops=allow_memory_ops,
                context=context,
                inside_control_flow=inside_control_flow,
            )
        return

    if isinstance(stmt, NAssign):
        _validate_expr(
            stmt.expr,
            allowed_model_calls=allowed_model_calls,
            allow_memory_ops=allow_memory_ops,
            context=context,
            inside_control_flow=inside_control_flow,
        )
        return

    if isinstance(stmt, NExprEffect):
        is_supported_memory_effect = (
            isinstance(stmt.expr, NBuiltinCall)
            and stmt.expr.op
            in (
                _ALLOWED_EXPR_STMT_BUILTINS
                | (frozenset({"mload"}) if allow_memory_ops else frozenset())
            )
        )
        if not is_supported_memory_effect:
            raise ParseError(
                f"{context} contains unsupported expression-statement "
                f"{type(stmt.expr).__name__}. Refuse to proceed with incomplete semantics."
            )
        _validate_expr(
            stmt.expr,
            allowed_model_calls=allowed_model_calls,
            allow_memory_ops=allow_memory_ops,
            context=context,
            inside_control_flow=inside_control_flow,
        )
        return

    if isinstance(stmt, NStore):
        if inside_control_flow and not allow_memory_ops:
            raise ParseError(
                f"{context} reaches restricted IR lowering with memory operation "
                f"inside conditional control flow"
            )
        _validate_expr(
            stmt.addr,
            allowed_model_calls=allowed_model_calls,
            allow_memory_ops=allow_memory_ops,
            context=context,
            inside_control_flow=inside_control_flow,
        )
        _validate_expr(
            stmt.value,
            allowed_model_calls=allowed_model_calls,
            allow_memory_ops=allow_memory_ops,
            context=context,
            inside_control_flow=inside_control_flow,
        )
        return

    if isinstance(stmt, NIf):
        _validate_expr(
            stmt.condition,
            allowed_model_calls=allowed_model_calls,
            allow_memory_ops=allow_memory_ops,
            context=context,
            inside_control_flow=True,
        )
        _validate_block(
            stmt.then_body,
            allowed_model_calls=allowed_model_calls,
            allow_memory_ops=allow_memory_ops,
            context=context,
            inside_control_flow=True,
        )
        return

    if isinstance(stmt, NSwitch):
        _validate_expr(
            stmt.discriminant,
            allowed_model_calls=allowed_model_calls,
            allow_memory_ops=allow_memory_ops,
            context=context,
            inside_control_flow=True,
        )
        for case in stmt.cases:
            _validate_block(
                case.body,
                allowed_model_calls=allowed_model_calls,
                allow_memory_ops=allow_memory_ops,
                context=context,
                inside_control_flow=True,
            )
        if stmt.default is not None:
            _validate_block(
                stmt.default,
                allowed_model_calls=allowed_model_calls,
                allow_memory_ops=allow_memory_ops,
                context=context,
                inside_control_flow=True,
            )
        return

    if isinstance(stmt, NFor):
        raise ParseError(
            f"{context} contains unsupported for-loop after simplification"
        )

    if isinstance(stmt, NLeave):
        raise ParseError("NLeave in restricted IR lowering — should have been inlined")

    if isinstance(stmt, NFunctionDef):
        # Local helper definitions are structural. Validation focuses on the
        # executable path; any still-live use of a local helper is rejected via
        # NLocalCall in expression position.
        return

    if isinstance(stmt, NBlock):
        _validate_block(
            stmt,
            allowed_model_calls=allowed_model_calls,
            allow_memory_ops=allow_memory_ops,
            context=context,
            inside_control_flow=inside_control_flow,
        )
        return

    assert_never(stmt)


def _validate_expr(
    expr: NExpr,
    *,
    allowed_model_calls: frozenset[str],
    allow_memory_ops: bool,
    context: str,
    inside_control_flow: bool,
) -> None:
    if isinstance(expr, (NConst, NRef)):
        return

    if isinstance(expr, NBuiltinCall):
        if (
            inside_control_flow
            and not allow_memory_ops
            and expr.op in _ALLOWED_EXPR_STMT_BUILTINS.union({"mload"})
        ):
            raise ParseError(
                f"{context} reaches restricted IR lowering with memory operation "
                f"inside conditional control flow"
            )
        for arg in expr.args:
            _validate_expr(
                arg,
                allowed_model_calls=allowed_model_calls,
                allow_memory_ops=allow_memory_ops,
                context=context,
                inside_control_flow=inside_control_flow,
            )
        return

    if isinstance(expr, NLocalCall):
        raise ParseError(
            f"{context} reaches restricted IR lowering with residual local helper "
            f"call {expr.name!r}. "
            f"All non-selected helpers must be inlined before restricted lowering."
        )

    if isinstance(expr, NTopLevelCall):
        if expr.name not in allowed_model_calls:
            raise ParseError(
                f"{context} reaches restricted IR lowering with non-selected "
                f"model call {expr.name!r}. "
                f"Only explicitly selected targets may remain as model calls."
            )
        for arg in expr.args:
            _validate_expr(
                arg,
                allowed_model_calls=allowed_model_calls,
                allow_memory_ops=allow_memory_ops,
                context=context,
                inside_control_flow=inside_control_flow,
            )
        return

    if isinstance(expr, NUnresolvedCall):
        raise ParseError(
            f"Unresolved call to {expr.name!r} in {context}; unresolved call is live"
        )

    if isinstance(expr, NIte):
        _validate_expr(
            expr.cond,
            allowed_model_calls=allowed_model_calls,
            allow_memory_ops=allow_memory_ops,
            context=context,
            inside_control_flow=inside_control_flow,
        )
        _validate_expr(
            expr.if_true,
            allowed_model_calls=allowed_model_calls,
            allow_memory_ops=allow_memory_ops,
            context=context,
            inside_control_flow=inside_control_flow,
        )
        _validate_expr(
            expr.if_false,
            allowed_model_calls=allowed_model_calls,
            allow_memory_ops=allow_memory_ops,
            context=context,
            inside_control_flow=inside_control_flow,
        )
        return

    assert_never(expr)
