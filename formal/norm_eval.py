"""
Interpreter for the normalized imperative IR.

Evaluates a ``NormalizedFunction`` with concrete integer arguments and
returns the function's return values.  Used for semantic equivalence
testing against the old pipeline's ``evaluate_function_model``.
"""

from __future__ import annotations

from collections.abc import Callable
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
    NLeave,
    NLocalCall,
    NormalizedFunction,
    NRef,
    NStmt,
    NSwitch,
    NTopLevelCall,
    NUnresolvedCall,
)
from yul_ast import EvaluationError, SymbolId

# ---------------------------------------------------------------------------
# u256 arithmetic (matches yul_to_lean.py semantics)
# ---------------------------------------------------------------------------

WORD_MOD: int = 2**256


def _u256(value: int) -> int:
    return value % WORD_MOD


# ---------------------------------------------------------------------------
# Builtin dispatch
# ---------------------------------------------------------------------------


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


def _eval_builtin(name: str, args: tuple[int, ...]) -> int:
    fn = _BUILTIN_DISPATCH.get((name, len(args)))
    if fn is not None:
        return fn(args)
    raise EvaluationError(f"Unsupported builtin {name!r}/{len(args)}")


# ---------------------------------------------------------------------------
# Leave signal
# ---------------------------------------------------------------------------


class _LeaveSignal(Exception):
    """Raised when ``leave`` is executed; caught at function boundary."""

    pass


# ---------------------------------------------------------------------------
# Evaluation context
# ---------------------------------------------------------------------------

_MAX_LOOP_ITERATIONS: int = 10_000


class _EvalCtx:
    """Mutable evaluation state for one function invocation."""

    def __init__(
        self,
        env: dict[SymbolId, int],
        memory: dict[int, int],
        func_table: dict[str, NormalizedFunction],
        call_stack: tuple[str, ...],
    ) -> None:
        self.env = env
        self.memory = memory
        self.func_table = func_table
        self.call_stack = call_stack


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def evaluate_normalized(
    func: NormalizedFunction,
    args: tuple[int, ...],
    *,
    function_table: dict[str, NormalizedFunction] | None = None,
) -> tuple[int, ...]:
    """Evaluate *func* with concrete *args*, returning its return values."""
    if len(args) != len(func.params):
        raise EvaluationError(
            f"Function {func.name!r} expects {len(func.params)} arg(s), "
            f"got {len(args)}"
        )

    env: dict[SymbolId, int] = {}
    for sid, val in zip(func.params, args):
        env[sid] = _u256(val)
    # Return variables default to 0.
    for sid in func.returns:
        env[sid] = 0

    ft: dict[str, NormalizedFunction] = dict(function_table) if function_table else {}
    ctx = _EvalCtx(env=env, memory={}, func_table=ft, call_stack=(func.name,))

    try:
        _exec_block(ctx, func.body)
    except _LeaveSignal:
        pass

    return tuple(ctx.env[sid] for sid in func.returns)


# ---------------------------------------------------------------------------
# Statement execution
# ---------------------------------------------------------------------------


def _exec_block(ctx: _EvalCtx, block: NBlock) -> None:
    for stmt in block.stmts:
        _exec_stmt(ctx, stmt)


def _exec_stmt(ctx: _EvalCtx, stmt: NStmt) -> None:
    if isinstance(stmt, NBind):
        if stmt.expr is not None:
            val = _eval_expr(ctx, stmt.expr)
            if len(stmt.targets) == 1:
                ctx.env[stmt.targets[0]] = _to_scalar(val)
            else:
                tup = _to_tuple(val, len(stmt.targets))
                for sid, v in zip(stmt.targets, tup):
                    ctx.env[sid] = v
        else:
            # Bare let — initialize to 0.
            for sid in stmt.targets:
                ctx.env[sid] = 0
        return

    if isinstance(stmt, NAssign):
        val = _eval_expr(ctx, stmt.expr)
        if len(stmt.targets) == 1:
            ctx.env[stmt.targets[0]] = _to_scalar(val)
        else:
            tup = _to_tuple(val, len(stmt.targets))
            for sid, v in zip(stmt.targets, tup):
                ctx.env[sid] = v
        return

    if isinstance(stmt, NExprEffect):
        _eval_expr(ctx, stmt.expr)
        return

    if isinstance(stmt, NIf):
        cond = _to_scalar(_eval_expr(ctx, stmt.condition))
        if cond != 0:
            _exec_block(ctx, stmt.then_body)
        return

    if isinstance(stmt, NSwitch):
        disc = _to_scalar(_eval_expr(ctx, stmt.discriminant))
        for case in stmt.cases:
            if case.value.value == disc:
                _exec_block(ctx, case.body)
                return
        if stmt.default is not None:
            _exec_block(ctx, stmt.default)
        return

    if isinstance(stmt, NFor):
        _exec_block(ctx, stmt.init)
        for _ in range(_MAX_LOOP_ITERATIONS):
            cond = _to_scalar(_eval_expr(ctx, stmt.condition))
            if cond == 0:
                return
            try:
                _exec_block(ctx, stmt.body)
            except _LeaveSignal:
                raise
            _exec_block(ctx, stmt.post)
        raise EvaluationError("For-loop exceeded maximum iteration count")

    if isinstance(stmt, NLeave):
        raise _LeaveSignal()

    if isinstance(stmt, NBlock):
        _exec_block(ctx, stmt)
        return

    if isinstance(stmt, NFunctionDef):
        # Function definitions are structural; not executed at runtime.
        return

    assert_never(stmt)


# ---------------------------------------------------------------------------
# Expression evaluation
# ---------------------------------------------------------------------------

_EvalResult = int | tuple[int, ...]


def _eval_expr(ctx: _EvalCtx, expr: NExpr) -> _EvalResult:
    if isinstance(expr, NConst):
        return _u256(expr.value)

    if isinstance(expr, NRef):
        if expr.symbol_id not in ctx.env:
            raise EvaluationError(f"Undefined variable {expr.name!r}")
        return ctx.env[expr.symbol_id]

    if isinstance(expr, NBuiltinCall):
        # mstore: side effect on memory, returns nothing meaningful.
        if expr.op == "mstore" and len(expr.args) == 2:
            addr = _to_scalar(_eval_expr(ctx, expr.args[0]))
            value = _to_scalar(_eval_expr(ctx, expr.args[1]))
            ctx.memory[_u256(addr)] = _u256(value)
            return 0

        # mload: read from memory.
        if expr.op == "mload" and len(expr.args) == 1:
            addr = _to_scalar(_eval_expr(ctx, expr.args[0]))
            return ctx.memory.get(_u256(addr), 0)

        args = tuple(_to_scalar(_eval_expr(ctx, a)) for a in expr.args)
        return _eval_builtin(expr.op, args)

    if isinstance(expr, (NLocalCall, NTopLevelCall)):
        name = expr.name
        if name not in ctx.func_table:
            raise EvaluationError(f"Unknown function {name!r}")
        if name in ctx.call_stack:
            raise EvaluationError(f"Recursive call to {name!r}")
        callee = ctx.func_table[name]
        args = tuple(_to_scalar(_eval_expr(ctx, a)) for a in expr.args)
        result = evaluate_normalized(
            callee,
            args,
            function_table=ctx.func_table,
        )
        if len(result) == 1:
            return result[0]
        return result

    if isinstance(expr, NUnresolvedCall):
        raise EvaluationError(f"Unresolved call to {expr.name!r}")

    assert_never(expr)


def _to_scalar(val: _EvalResult) -> int:
    if isinstance(val, tuple):
        if len(val) == 1:
            return val[0]
        raise EvaluationError(f"Expected scalar, got {len(val)}-tuple")
    return val


def _to_tuple(val: _EvalResult, n: int) -> tuple[int, ...]:
    if isinstance(val, int):
        if n == 1:
            return (val,)
        raise EvaluationError(f"Expected {n}-tuple, got scalar")
    if len(val) != n:
        raise EvaluationError(f"Expected {n}-tuple, got {len(val)}-tuple")
    return val
