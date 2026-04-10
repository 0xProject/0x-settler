"""
Evaluator for the non-SSA restricted IR.

Used for semantic equivalence testing against the normalized IR
evaluator and the old pipeline's ``evaluate_function_model``.
"""

from __future__ import annotations

from collections.abc import Callable

from restricted_ir import (
    RAssignment,
    RBranch,
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
from yul_ast import EvaluationError, SymbolId

# ---------------------------------------------------------------------------
# u256 arithmetic (same as norm_eval.py)
# ---------------------------------------------------------------------------

WORD_MOD: int = 2**256


def _u256(value: int) -> int:
    return value % WORD_MOD


def _div(a: tuple[int, ...]) -> int:
    aa, bb = _u256(a[0]), _u256(a[1])
    return 0 if bb == 0 else aa // bb


def _mod(a: tuple[int, ...]) -> int:
    aa, bb = _u256(a[0]), _u256(a[1])
    return 0 if bb == 0 else aa % bb


def _shl(a: tuple[int, ...]) -> int:
    shift, value = _u256(a[0]), _u256(a[1])
    return _u256(value << shift) if shift < 256 else 0


def _shr(a: tuple[int, ...]) -> int:
    shift, value = _u256(a[0]), _u256(a[1])
    return value >> shift if shift < 256 else 0


def _clz(a: tuple[int, ...]) -> int:
    value = _u256(a[0])
    return 256 if value == 0 else 255 - (value.bit_length() - 1)


def _mulmod(a: tuple[int, ...]) -> int:
    aa, bb, nn = _u256(a[0]), _u256(a[1]), _u256(a[2])
    return 0 if nn == 0 else (aa * bb) % nn


_BUILTIN_DISPATCH: dict[tuple[str, int], Callable[[tuple[int, ...]], int]] = {
    ("add", 2): lambda a: _u256(_u256(a[0]) + _u256(a[1])),
    ("sub", 2): lambda a: _u256(_u256(a[0]) + WORD_MOD - _u256(a[1])),
    ("mul", 2): lambda a: _u256(_u256(a[0]) * _u256(a[1])),
    ("div", 2): _div,
    ("mod", 2): _mod,
    ("not", 1): lambda a: WORD_MOD - 1 - _u256(a[0]),
    ("or", 2): lambda a: _u256(a[0]) | _u256(a[1]),
    ("and", 2): lambda a: _u256(a[0]) & _u256(a[1]),
    ("eq", 2): lambda a: 1 if _u256(a[0]) == _u256(a[1]) else 0,
    ("iszero", 1): lambda a: 1 if _u256(a[0]) == 0 else 0,
    ("shl", 2): _shl,
    ("shr", 2): _shr,
    ("clz", 1): _clz,
    ("lt", 2): lambda a: 1 if _u256(a[0]) < _u256(a[1]) else 0,
    ("gt", 2): lambda a: 1 if _u256(a[0]) > _u256(a[1]) else 0,
    ("mulmod", 3): _mulmod,
}


# ---------------------------------------------------------------------------
# Expression evaluation
# ---------------------------------------------------------------------------


def _eval_expr(
    expr: RExpr,
    env: dict[SymbolId, int],
    model_table: dict[str, RestrictedFunction] | None = None,
) -> int:
    if isinstance(expr, RConst):
        return _u256(expr.value)

    if isinstance(expr, RRef):
        if expr.symbol_id not in env:
            raise EvaluationError(f"Undefined variable {expr.name!r}")
        return env[expr.symbol_id]

    if isinstance(expr, RBuiltinCall):
        args = tuple(_eval_expr(a, env, model_table) for a in expr.args)
        fn = _BUILTIN_DISPATCH.get((expr.op, len(args)))
        if fn is None:
            raise EvaluationError(f"Unsupported builtin {expr.op!r}/{len(args)}")
        return _u256(fn(args))

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


# ---------------------------------------------------------------------------
# Statement evaluation
# ---------------------------------------------------------------------------


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

            # Evaluate branch assignments in a local scope.
            branch_env = dict(env)
            _eval_block(branch.assignments, branch_env, model_table)

            # Extract outputs into outer scope.
            for out_sid, out_expr in zip(stmt.output_targets, branch.output_exprs):
                env[out_sid] = _eval_expr(out_expr, branch_env, model_table)


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def evaluate_restricted(
    func: RestrictedFunction,
    args: tuple[int, ...],
    *,
    model_table: dict[str, RestrictedFunction] | None = None,
) -> tuple[int, ...]:
    """Evaluate a restricted IR function with concrete arguments."""
    if len(args) != len(func.params):
        raise EvaluationError(
            f"Function {func.name!r} expects {len(func.params)} arg(s), "
            f"got {len(args)}"
        )

    env: dict[SymbolId, int] = {}
    for sid, val in zip(func.params, args):
        env[sid] = _u256(val)
    for sid in func.returns:
        env[sid] = 0

    _eval_block(func.body, env, model_table)

    return tuple(env[sid] for sid in func.returns)
