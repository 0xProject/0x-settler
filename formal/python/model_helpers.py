from __future__ import annotations

from typing import Callable, assert_never

from .evm_builtins import OP_TO_LEAN_HELPER, OP_TO_OPCODE
from .model_ir import (
    Assignment,
    Call,
    ConditionalBlock,
    ConditionalBranch,
    Expr,
    FunctionModel,
    IntLit,
    Ite,
    ModelStatement,
    Project,
    Var,
)

# ---------------------------------------------------------------------------
# Generic Expr walkers
# ---------------------------------------------------------------------------


def for_each_model_expr(expr: Expr, fn: Callable[[Expr], None]) -> None:
    """Pre-order traversal visiting every Expr node."""
    fn(expr)
    if isinstance(expr, (IntLit, Var)):
        pass
    elif isinstance(expr, Call):
        for arg in expr.args:
            for_each_model_expr(arg, fn)
    elif isinstance(expr, Ite):
        for_each_model_expr(expr.cond, fn)
        for_each_model_expr(expr.if_true, fn)
        for_each_model_expr(expr.if_false, fn)
    elif isinstance(expr, Project):
        for_each_model_expr(expr.inner, fn)
    else:
        assert_never(expr)


def map_model_expr(expr: Expr, fn: Callable[[Expr], Expr]) -> Expr:
    """Bottom-up map: recurse children first, then apply *fn* to result."""
    if isinstance(expr, (IntLit, Var)):
        return fn(expr)
    if isinstance(expr, Call):
        return fn(Call(expr.name, tuple(map_model_expr(a, fn) for a in expr.args)))
    if isinstance(expr, Ite):
        return fn(
            Ite(
                map_model_expr(expr.cond, fn),
                map_model_expr(expr.if_true, fn),
                map_model_expr(expr.if_false, fn),
            )
        )
    if isinstance(expr, Project):
        return fn(Project(expr.index, expr.total, map_model_expr(expr.inner, fn)))
    assert_never(expr)


# ---------------------------------------------------------------------------
# Statement walkers
# ---------------------------------------------------------------------------


def walk_model_exprs_in_stmt(
    stmt: ModelStatement,
    visit: Callable[[Expr], None],
) -> None:
    """Visit every expression position reachable from a model statement."""
    if isinstance(stmt, Assignment):
        visit(stmt.expr)
        return
    if isinstance(stmt, ConditionalBlock):
        visit(stmt.condition)
        _walk_model_exprs_in_branch(stmt.then_branch, visit)
        _walk_model_exprs_in_branch(stmt.else_branch, visit)
        return
    assert_never(stmt)


def _walk_model_exprs_in_branch(
    branch: ConditionalBranch,
    visit: Callable[[Expr], None],
) -> None:
    for stmt in branch.assignments:
        walk_model_exprs_in_stmt(stmt, visit)
    for expr in branch.outputs:
        visit(expr)


# ---------------------------------------------------------------------------
# Derived helpers (built on the generic walkers above)
# ---------------------------------------------------------------------------


def _collect_ops(expr: Expr) -> list[str]:
    out: list[str] = []

    def visit(e: Expr) -> None:
        if isinstance(e, Call) and e.name in OP_TO_OPCODE:
            out.append(e.name)

    for_each_model_expr(expr, visit)
    return out


def collect_ops_from_statement(stmt: ModelStatement) -> list[str]:
    """Collect opcodes from an Assignment or ConditionalBlock."""
    ops: list[str] = []
    walk_model_exprs_in_stmt(stmt, lambda expr: ops.extend(_collect_ops(expr)))
    return ops


def collect_model_opcodes(models: list[FunctionModel]) -> list[str]:
    """Collect ordered unique opcodes used across all models."""
    raw_ops: list[str] = []
    for model in models:
        for stmt in model.assignments:
            raw_ops.extend(collect_ops_from_statement(stmt))
    seen: dict[str, None] = {}
    for name in raw_ops:
        seen.setdefault(OP_TO_OPCODE[name])
    return list(seen)


def model_call_names_in_stmt(stmt: ModelStatement) -> set[str]:
    """Collect non-builtin call names from a model statement."""
    names: set[str] = set()

    def visit(e: Expr) -> None:
        if isinstance(e, Call) and e.name not in OP_TO_LEAN_HELPER:
            names.add(e.name)

    walk_model_exprs_in_stmt(stmt, lambda expr: for_each_model_expr(expr, visit))
    return names


def expr_size(expr: Expr) -> int:
    count = 0

    def visit(_: Expr) -> None:
        nonlocal count
        count += 1

    for_each_model_expr(expr, visit)
    return count


def replace_expr(expr: Expr, replacements: dict[Expr, str]) -> Expr:
    def fn(e: Expr) -> Expr:
        return Var(replacements[e]) if e in replacements else e

    return map_model_expr(expr, fn)


def expr_vars(expr: Expr) -> set[str]:
    out: set[str] = set()

    def visit(e: Expr) -> None:
        if isinstance(e, Var):
            out.add(e.name)

    for_each_model_expr(expr, visit)
    return out


def collect_model_binders(model: FunctionModel) -> list[str]:
    binders = [*model.param_names, *model.return_names]
    for stmt in model.assignments:
        _collect_binders_from_stmt(stmt, binders)
    return binders


def _collect_binders_from_stmt(stmt: ModelStatement, out: list[str]) -> None:
    if isinstance(stmt, Assignment):
        out.append(stmt.target)
    elif isinstance(stmt, ConditionalBlock):
        out.extend(stmt.output_vars)
        for s in stmt.then_branch.assignments:
            _collect_binders_from_stmt(s, out)
        for s in stmt.else_branch.assignments:
            _collect_binders_from_stmt(s, out)
    else:
        assert_never(stmt)
