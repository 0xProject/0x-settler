from __future__ import annotations

from typing import assert_never

from ..evm_builtins import OP_TO_LEAN_HELPER
from ..evm_builtins import eval_pure_builtin as _eval_builtin
from ..evm_builtins import u256
from ..model_ir import (
    Assignment,
    Call,
    ConditionalBlock,
    Expr,
    FunctionModel,
    IntLit,
    Ite,
    ModelStatement,
    ModelValue,
    Project,
    Var,
)
from ..yul_ast import EvaluationError


def _expect_scalar(value: ModelValue, *, context: str) -> int:
    if isinstance(value, tuple):
        raise EvaluationError(f"{context} expected a scalar value, got tuple {value!r}")
    return value


def _expect_tuple(value: ModelValue, *, size: int, context: str) -> tuple[int, ...]:
    if not isinstance(value, tuple):
        raise EvaluationError(
            f"{context} expected a {size}-tuple, got scalar {value!r}"
        )
    if len(value) != size:
        raise EvaluationError(
            f"{context} expected a {size}-tuple, got {len(value)} values: {value!r}"
        )
    return value


def build_model_table(
    models: list[FunctionModel] | tuple[FunctionModel, ...],
) -> dict[str, FunctionModel]:
    table: dict[str, FunctionModel] = {}
    for model in models:
        if model.fn_name in table:
            raise EvaluationError(f"Duplicate FunctionModel name {model.fn_name!r}")
        table[model.fn_name] = model
    return table


def evaluate_model_expr(
    expr: Expr,
    env: dict[str, int],
    *,
    model_table: dict[str, FunctionModel] | None = None,
    call_stack: tuple[str, ...] = (),
) -> ModelValue:
    if isinstance(expr, IntLit):
        return u256(expr.value)
    if isinstance(expr, Var):
        try:
            return env[expr.name]
        except KeyError as err:
            raise EvaluationError(f"Undefined model variable {expr.name!r}") from err
    if isinstance(expr, Project):
        values = _expect_tuple(
            evaluate_model_expr(
                expr.inner,
                env,
                model_table=model_table,
                call_stack=call_stack,
            ),
            size=expr.total,
            context=f"Project({expr.index}, {expr.total}) projection",
        )
        try:
            return values[expr.index]
        except IndexError as err:
            raise EvaluationError(
                f"Project({expr.index}, {expr.total}) requested index {expr.index}, "
                f"but only {len(values)} value(s) exist"
            ) from err
    if isinstance(expr, Ite):
        cond = _expect_scalar(
            evaluate_model_expr(
                expr.cond,
                env,
                model_table=model_table,
                call_stack=call_stack,
            ),
            context="Ite condition",
        )
        branch = expr.if_true if cond != 0 else expr.if_false
        return evaluate_model_expr(
            branch,
            env,
            model_table=model_table,
            call_stack=call_stack,
        )
    if not isinstance(expr, Call):
        assert_never(expr)

    arg_values = tuple(
        evaluate_model_expr(arg, env, model_table=model_table, call_stack=call_stack)
        for arg in expr.args
    )

    if expr.name in OP_TO_LEAN_HELPER:
        return _eval_builtin(
            expr.name,
            tuple(
                _expect_scalar(value, context=f"builtin {expr.name}")
                for value in arg_values
            ),
        )

    if model_table is None or expr.name not in model_table:
        raise EvaluationError(f"Unsupported model call {expr.name!r}")

    model = model_table[expr.name]
    if expr.name in call_stack:
        cycle = " -> ".join((*call_stack, expr.name))
        raise EvaluationError(f"Recursive model call cycle detected: {cycle}")
    result = evaluate_function_model(
        model,
        tuple(
            _expect_scalar(value, context=f"model call {expr.name}")
            for value in arg_values
        ),
        model_table=model_table,
        call_stack=(*call_stack, expr.name),
    )
    if len(result) == 1:
        return result[0]
    return result


def _evaluate_statement_block(
    statements: tuple[ModelStatement, ...],
    env: dict[str, int],
    *,
    model_table: dict[str, FunctionModel] | None = None,
    call_stack: tuple[str, ...] = (),
) -> dict[str, int]:
    scope = dict(env)

    for stmt in statements:
        if isinstance(stmt, Assignment):
            scope[stmt.target] = _expect_scalar(
                evaluate_model_expr(
                    stmt.expr,
                    scope,
                    model_table=model_table,
                    call_stack=call_stack,
                ),
                context=f"assignment to {stmt.target!r}",
            )
            continue

        if not isinstance(stmt, ConditionalBlock):
            assert_never(stmt)

        condition = _expect_scalar(
            evaluate_model_expr(
                stmt.condition,
                scope,
                model_table=model_table,
                call_stack=call_stack,
            ),
            context="conditional",
        )

        branch = stmt.then_branch if condition != 0 else stmt.else_branch
        branch_scope = _evaluate_statement_block(
            branch.assignments,
            scope,
            model_table=model_table,
            call_stack=call_stack,
        )
        for target, out_expr in zip(stmt.output_vars, branch.outputs, strict=True):
            scope[target] = _expect_scalar(
                evaluate_model_expr(
                    out_expr,
                    branch_scope,
                    model_table=model_table,
                    call_stack=call_stack,
                ),
                context=f"branch output for {target!r}",
            )

    return scope


def evaluate_function_model(
    model: FunctionModel,
    args: tuple[int, ...],
    *,
    model_table: dict[str, FunctionModel] | None = None,
    call_stack: tuple[str, ...] = (),
) -> tuple[int, ...]:
    if len(args) != len(model.param_names):
        raise EvaluationError(
            f"Model {model.fn_name!r} expects {len(model.param_names)} argument(s), "
            f"got {len(args)}"
        )

    env = {
        param_name: u256(value)
        for param_name, value in zip(model.param_names, args, strict=True)
    }
    final_env = _evaluate_statement_block(
        model.assignments,
        env,
        model_table=model_table,
        call_stack=call_stack,
    )
    try:
        return tuple(final_env[name] for name in model.return_names)
    except KeyError as err:
        raise EvaluationError(
            f"Model {model.fn_name!r} did not produce one of the declared return variables "
            f"{model.return_names!r}"
        ) from err
