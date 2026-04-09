"""
Interpreter for the normalized imperative IR.

Evaluates a ``NormalizedFunction`` with concrete integer arguments and
returns the function's return values.  Used for semantic equivalence
testing against the old pipeline's ``evaluate_function_model``.

Key semantics:
- Memory is shared across all calls (Yul semantics).
- Local helper calls are dispatched by ``SymbolId``, not by name.
- Top-level calls are dispatched by name.
- ``leave`` is modeled as an exception caught at function boundary.
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
# Memory builtins — recognized by name regardless of call classification,
# since the resolver's _SUPPORTED_OPS_FROZENSET does not include them.
# ---------------------------------------------------------------------------

_MEMORY_OPS: frozenset[str] = frozenset({"mstore", "mload"})


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
    """Mutable evaluation state threaded through all calls."""

    def __init__(
        self,
        env: dict[SymbolId, int],
        memory: dict[int, int],
        local_funcs: dict[SymbolId, NFunctionDef],
        named_funcs: dict[str, NormalizedFunction],
        call_stack: tuple[str, ...],
    ) -> None:
        self.env = env
        self.memory = memory
        self.local_funcs = local_funcs
        self.named_funcs = named_funcs
        self.call_stack = call_stack


# ---------------------------------------------------------------------------
# Collect nested function definitions from a block
# ---------------------------------------------------------------------------


def _collect_local_funcs(block: NBlock) -> dict[SymbolId, NFunctionDef]:
    """Collect all ``NFunctionDef`` nodes from a block (non-recursive).

    Yul functions are hoisted within their enclosing block, so all
    function definitions at the top level of *block* are visible
    throughout the block.  Nested functions inside those bodies are
    NOT included — they will be collected when the inner function
    is called.
    """
    result: dict[SymbolId, NFunctionDef] = {}
    for stmt in block.stmts:
        if isinstance(stmt, NFunctionDef):
            result[stmt.symbol_id] = stmt
    return result


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def evaluate_normalized(
    func: NormalizedFunction,
    args: tuple[int, ...],
    *,
    function_table: dict[str, NormalizedFunction] | None = None,
    memory: dict[int, int] | None = None,
    call_stack: tuple[str, ...] = (),
) -> tuple[int, ...]:
    """Evaluate *func* with concrete *args*, returning its return values.

    *function_table* maps function names to ``NormalizedFunction`` for
    top-level (cross-function) calls.  Local helper calls are resolved
    by ``SymbolId`` from ``NFunctionDef`` nodes in the function body.

    *memory* is the shared Yul memory (mutated in-place by mstore).
    Pass an existing dict to share memory across calls.

    *call_stack* tracks active function names for recursion detection.
    """
    if len(args) != len(func.params):
        raise EvaluationError(
            f"Function {func.name!r} expects {len(func.params)} arg(s), "
            f"got {len(args)}"
        )

    if func.name in call_stack:
        raise EvaluationError(f"Recursive call to {func.name!r}")

    env: dict[SymbolId, int] = {}
    for sid, val in zip(func.params, args):
        env[sid] = _u256(val)
    # Return variables default to 0.
    for sid in func.returns:
        env[sid] = 0

    shared_memory = memory if memory is not None else {}
    named: dict[str, NormalizedFunction] = (
        dict(function_table) if function_table else {}
    )
    local = _collect_local_funcs(func.body)

    ctx = _EvalCtx(
        env=env,
        memory=shared_memory,
        local_funcs=local,
        named_funcs=named,
        call_stack=call_stack + (func.name,),
    )

    try:
        _exec_block(ctx, func.body)
    except _LeaveSignal:
        pass

    return tuple(ctx.env[sid] for sid in func.returns)


# ---------------------------------------------------------------------------
# Statement execution
# ---------------------------------------------------------------------------


def _exec_block(ctx: _EvalCtx, block: NBlock) -> None:
    # Hoist function definitions — Yul makes them visible throughout
    # their enclosing block.  SymbolId keys ensure no collisions.
    for stmt in block.stmts:
        if isinstance(stmt, NFunctionDef):
            ctx.local_funcs[stmt.symbol_id] = stmt
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
        return _eval_call_by_name(ctx, expr.op, expr.args)

    if isinstance(expr, NLocalCall):
        # Look up by SymbolId — avoids name collisions across scopes.
        if expr.symbol_id not in ctx.local_funcs:
            raise EvaluationError(
                f"Unknown local function {expr.name!r} " f"(symbol {expr.symbol_id!r})"
            )
        fdef = ctx.local_funcs[expr.symbol_id]
        return _call_function_def(ctx, fdef, expr.args)

    if isinstance(expr, NTopLevelCall):
        # Memory builtins may appear as top-level calls if not in
        # the resolver's builtin set.
        if expr.name in _MEMORY_OPS:
            return _eval_call_by_name(ctx, expr.name, expr.args)
        if expr.name not in ctx.named_funcs:
            raise EvaluationError(f"Unknown top-level function {expr.name!r}")
        callee = ctx.named_funcs[expr.name]
        args = tuple(_to_scalar(_eval_expr(ctx, a)) for a in expr.args)
        result = evaluate_normalized(
            callee,
            args,
            function_table=ctx.named_funcs,
            memory=ctx.memory,
            call_stack=ctx.call_stack,
        )
        if len(result) == 1:
            return result[0]
        return result

    if isinstance(expr, NUnresolvedCall):
        # Memory builtins may be unresolved if not in the resolver's
        # builtin set.  Try them before giving up.
        if expr.name in _MEMORY_OPS or (expr.name, len(expr.args)) in _BUILTIN_DISPATCH:
            return _eval_call_by_name(ctx, expr.name, expr.args)
        raise EvaluationError(f"Unresolved call to {expr.name!r}")

    assert_never(expr)


def _eval_call_by_name(
    ctx: _EvalCtx, name: str, args: tuple[NExpr, ...]
) -> _EvalResult:
    """Evaluate a call to a builtin or memory op by name."""
    # mstore: side effect on memory.
    if name == "mstore" and len(args) == 2:
        addr = _to_scalar(_eval_expr(ctx, args[0]))
        value = _to_scalar(_eval_expr(ctx, args[1]))
        ctx.memory[_u256(addr)] = _u256(value)
        return 0

    # mload: read from memory.
    if name == "mload" and len(args) == 1:
        addr = _to_scalar(_eval_expr(ctx, args[0]))
        return ctx.memory.get(_u256(addr), 0)

    # Regular arithmetic builtin.
    evaluated = tuple(_to_scalar(_eval_expr(ctx, a)) for a in args)
    return _eval_builtin(name, evaluated)


def _call_function_def(
    ctx: _EvalCtx, fdef: NFunctionDef, args: tuple[NExpr, ...]
) -> _EvalResult:
    """Call a local helper function, sharing memory with the caller."""
    nf = NormalizedFunction(
        name=fdef.name,
        params=fdef.params,
        param_names=fdef.param_names,
        returns=fdef.returns,
        return_names=fdef.return_names,
        body=fdef.body,
    )
    evaluated_args = tuple(_to_scalar(_eval_expr(ctx, a)) for a in args)
    result = evaluate_normalized(
        nf,
        evaluated_args,
        function_table=ctx.named_funcs,
        memory=ctx.memory,
        call_stack=ctx.call_stack,
    )
    if len(result) == 1:
        return result[0]
    return result


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
