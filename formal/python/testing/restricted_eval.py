"""
Evaluator for the non-SSA restricted IR.

Test-only support for semantic equivalence checks.
"""

from __future__ import annotations

from ..evm_builtins import eval_pure_builtin, u256
from ..restricted_ir import (
    RAssignment,
    RBuiltinCall,
    RCallAssign,
    RConditionalBlock,
    RConst,
    RestrictedFunction,
    RExpr,
    RIte,
    RModelCall,
    RRef,
    RStatement,
)
from ..yul_ast import EvaluationError, SymbolId


def _eval_expr(
    expr: RExpr,
    env: dict[SymbolId, int],
    model_table: dict[str, RestrictedFunction] | None = None,
) -> int:
    if isinstance(expr, RConst):
        return u256(expr.value)

    if isinstance(expr, RRef):
        if expr.symbol_id not in env:
            raise EvaluationError(f"Undefined variable {expr.name!r}")
        return env[expr.symbol_id]

    if isinstance(expr, RBuiltinCall):
        args = tuple(_eval_expr(a, env, model_table) for a in expr.args)
        return eval_pure_builtin(expr.op, args)

    if isinstance(expr, RModelCall):
        if model_table is None or expr.name not in model_table:
            raise EvaluationError(f"Unknown model function {expr.name!r}")
        callee = model_table[expr.name]
        if len(callee.returns) != 1:
            raise EvaluationError(
                f"Scalar model call to {expr.name!r} with {len(callee.returns)} returns"
            )
        args = tuple(_eval_expr(a, env, model_table) for a in expr.args)
        return evaluate_restricted(callee, args, model_table=model_table)[0]

    if isinstance(expr, RIte):
        cond = _eval_expr(expr.cond, env, model_table)
        if cond != 0:
            return _eval_expr(expr.if_true, env, model_table)
        return _eval_expr(expr.if_false, env, model_table)

    raise EvaluationError(f"Unexpected expression: {type(expr).__name__}")


def _eval_block(
    stmts: tuple[RStatement, ...],
    env: dict[SymbolId, int],
    model_table: dict[str, RestrictedFunction] | None = None,
) -> None:
    for stmt in stmts:
        if isinstance(stmt, RAssignment):
            env[stmt.target] = _eval_expr(stmt.expr, env, model_table)

        elif isinstance(stmt, RCallAssign):
            if model_table is None or stmt.callee not in model_table:
                raise EvaluationError(f"Unknown model function {stmt.callee!r}")
            callee = model_table[stmt.callee]
            args = tuple(_eval_expr(a, env, model_table) for a in stmt.args)
            values = evaluate_restricted(callee, args, model_table=model_table)
            if len(values) != len(stmt.targets):
                raise EvaluationError(
                    f"Call to {stmt.callee!r} returned {len(values)} value(s), "
                    f"expected {len(stmt.targets)}"
                )
            for sid, value in zip(stmt.targets, values):
                env[sid] = value

        elif isinstance(stmt, RConditionalBlock):
            cond = _eval_expr(stmt.condition, env, model_table)
            branch = stmt.then_branch if cond != 0 else stmt.else_branch

            branch_env = dict(env)
            _eval_block(branch.assignments, branch_env, model_table)

            for out_sid, out_expr in zip(stmt.output_targets, branch.output_exprs):
                env[out_sid] = _eval_expr(out_expr, branch_env, model_table)


def evaluate_restricted(
    func: RestrictedFunction,
    args: tuple[int, ...],
    *,
    model_table: dict[str, RestrictedFunction] | None = None,
) -> tuple[int, ...]:
    if len(args) != len(func.params):
        raise EvaluationError(
            f"Function {func.name!r} expects {len(func.params)} arg(s), "
            f"got {len(args)}"
        )

    env: dict[SymbolId, int] = {}
    for sid, val in zip(func.params, args):
        env[sid] = u256(val)
    for sid in func.returns:
        env[sid] = 0

    _eval_block(func.body, env, model_table)

    return tuple(env[sid] for sid in func.returns)
