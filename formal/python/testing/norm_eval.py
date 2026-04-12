"""
Interpreter for the normalized imperative IR.

Test-only support for semantic equivalence checks.
"""

from __future__ import annotations

from typing import assert_never

from ..evm_builtins import eval_pure_builtin, u256
from ..norm_ir import (
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
    NStore,
    NSwitch,
    NTopLevelCall,
    NUnresolvedCall,
)
from ..yul_ast import EvaluationError, SymbolId


class _LeaveSignal(Exception):
    """Raised when ``leave`` is executed; caught at function boundary."""

    pass


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


def _collect_local_funcs(block: NBlock) -> dict[SymbolId, NFunctionDef]:
    return {fdef.symbol_id: fdef for fdef in block.defs}


def evaluate_normalized(
    func: NormalizedFunction | NFunctionDef,
    args: tuple[int, ...],
    *,
    function_table: dict[str, NormalizedFunction] | None = None,
    enclosing_local_funcs: dict[SymbolId, NFunctionDef] | None = None,
    memory: dict[int, int] | None = None,
    call_stack: tuple[str, ...] = (),
) -> tuple[int, ...]:
    if len(args) != len(func.params):
        raise EvaluationError(
            f"Function {func.name!r} expects {len(func.params)} arg(s), "
            f"got {len(args)}"
        )

    if func.name in call_stack:
        raise EvaluationError(f"Recursive call to {func.name!r}")

    env: dict[SymbolId, int] = {}
    for sid, val in zip(func.params, args):
        env[sid] = u256(val)
    for sid in func.returns:
        env[sid] = 0

    shared_memory = memory if memory is not None else {}
    named: dict[str, NormalizedFunction] = (
        dict(function_table) if function_table else {}
    )
    local: dict[SymbolId, NFunctionDef] = (
        dict(enclosing_local_funcs) if enclosing_local_funcs else {}
    )
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


def _exec_block(ctx: _EvalCtx, block: NBlock) -> None:
    for fdef in block.defs:
        ctx.local_funcs[fdef.symbol_id] = fdef
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

    if isinstance(stmt, NStore):
        addr = _to_scalar(_eval_expr(ctx, stmt.addr))
        value = _to_scalar(_eval_expr(ctx, stmt.value))
        ctx.memory[u256(addr)] = u256(value)
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
            if stmt.condition_setup is not None:
                _exec_block(ctx, stmt.condition_setup)
            cond = _to_scalar(_eval_expr(ctx, stmt.condition))
            if cond == 0:
                return
            _exec_block(ctx, stmt.body)
            _exec_block(ctx, stmt.post)
        raise EvaluationError("For-loop exceeded maximum iteration count")

    if isinstance(stmt, NLeave):
        raise _LeaveSignal()

    if isinstance(stmt, NBlock):
        _exec_block(ctx, stmt)
        return

    assert_never(stmt)


_EvalResult = int | tuple[int, ...]


def _eval_expr(ctx: _EvalCtx, expr: NExpr) -> _EvalResult:
    if isinstance(expr, NConst):
        return u256(expr.value)

    if isinstance(expr, NRef):
        if expr.symbol_id not in ctx.env:
            raise EvaluationError(f"Undefined variable {expr.name!r}")
        return ctx.env[expr.symbol_id]

    if isinstance(expr, NBuiltinCall):
        return _eval_call_by_name(ctx, expr.op, expr.args)

    if isinstance(expr, NLocalCall):
        if expr.symbol_id not in ctx.local_funcs:
            raise EvaluationError(
                f"Unknown local function {expr.name!r} (symbol {expr.symbol_id!r})"
            )
        fdef = ctx.local_funcs[expr.symbol_id]
        return _call_function_def(ctx, fdef, expr.args)

    if isinstance(expr, NTopLevelCall):
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
        raise EvaluationError(f"Unresolved call to {expr.name!r}")

    if isinstance(expr, NIte):
        cond = _to_scalar(_eval_expr(ctx, expr.cond))
        if cond != 0:
            return _eval_expr(ctx, expr.if_true)
        return _eval_expr(ctx, expr.if_false)

    assert_never(expr)


def _eval_call_by_name(
    ctx: _EvalCtx, name: str, args: tuple[NExpr, ...]
) -> _EvalResult:
    if name == "mstore" and len(args) == 2:
        addr = _to_scalar(_eval_expr(ctx, args[0]))
        value = _to_scalar(_eval_expr(ctx, args[1]))
        ctx.memory[u256(addr)] = u256(value)
        return 0

    if name == "mload" and len(args) == 1:
        addr = _to_scalar(_eval_expr(ctx, args[0]))
        return ctx.memory.get(u256(addr), 0)

    evaluated = tuple(_to_scalar(_eval_expr(ctx, a)) for a in args)
    return eval_pure_builtin(name, evaluated)


def _call_function_def(
    ctx: _EvalCtx, fdef: NFunctionDef, args: tuple[NExpr, ...]
) -> _EvalResult:
    evaluated_args = tuple(_to_scalar(_eval_expr(ctx, a)) for a in args)
    result = evaluate_normalized(
        fdef,
        evaluated_args,
        function_table=ctx.named_funcs,
        enclosing_local_funcs=ctx.local_funcs,
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
