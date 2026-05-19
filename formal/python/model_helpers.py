from __future__ import annotations

from typing import Callable, assert_never

from .evm_builtins import OP_TO_LEAN_HELPER, OP_TO_OPCODE
from .expr_walk import for_each_expr as for_each_model_expr
from .expr_walk import map_expr as _map_model_expr
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
# Statement walkers
# ---------------------------------------------------------------------------


def for_each_model_stmt(
    stmt: ModelStatement,
    visit: Callable[[ModelStatement], None],
) -> None:
    """Pre-order traversal over model statements and nested branch statements."""
    visit(stmt)
    if isinstance(stmt, Assignment):
        return
    if isinstance(stmt, ConditionalBlock):
        for sub_stmt in stmt.then_branch.assignments:
            for_each_model_stmt(sub_stmt, visit)
        for sub_stmt in stmt.else_branch.assignments:
            for_each_model_stmt(sub_stmt, visit)
        return
    assert_never(stmt)


def for_each_model_stmt_expr(
    stmt: ModelStatement,
    visit: Callable[[Expr], None],
) -> None:
    """Visit every direct expression slot attached to one model statement."""
    if isinstance(stmt, Assignment):
        visit(stmt.expr)
        return
    if isinstance(stmt, ConditionalBlock):
        visit(stmt.condition)
        for expr in stmt.then_branch.outputs:
            visit(expr)
        for expr in stmt.else_branch.outputs:
            visit(expr)
        return
    assert_never(stmt)


def walk_model_exprs_in_stmt(
    stmt: ModelStatement,
    visit: Callable[[Expr], None],
) -> None:
    """Visit every expression position reachable from a model statement."""

    def walk_stmt(current: ModelStatement) -> None:
        for_each_model_stmt_expr(current, visit)

    for_each_model_stmt(stmt, walk_stmt)


def map_model_branch(
    branch: ConditionalBranch,
    *,
    map_stmt_fn: Callable[[ModelStatement], ModelStatement],
    map_expr_fn: Callable[[Expr], Expr],
) -> ConditionalBranch:
    return ConditionalBranch(
        assignments=tuple(map_stmt_fn(stmt) for stmt in branch.assignments),
        outputs=tuple(map_expr_fn(expr) for expr in branch.outputs),
    )


def map_model_stmt(
    stmt: ModelStatement,
    *,
    map_expr_fn: Callable[[Expr], Expr],
    map_branch_fn: Callable[[ConditionalBranch], ConditionalBranch] | None = None,
) -> ModelStatement:
    """Map one model statement structurally."""
    if isinstance(stmt, Assignment):
        return Assignment(target=stmt.target, expr=map_expr_fn(stmt.expr))
    if isinstance(stmt, ConditionalBlock):

        def default_branch_map(branch: ConditionalBranch) -> ConditionalBranch:
            return map_model_branch(
                branch,
                map_stmt_fn=lambda sub_stmt: map_model_stmt(
                    sub_stmt,
                    map_expr_fn=map_expr_fn,
                    map_branch_fn=map_branch_fn,
                ),
                map_expr_fn=map_expr_fn,
            )

        branch_map = map_branch_fn if map_branch_fn is not None else default_branch_map
        return ConditionalBlock(
            condition=map_expr_fn(stmt.condition),
            output_vars=stmt.output_vars,
            then_branch=branch_map(stmt.then_branch),
            else_branch=branch_map(stmt.else_branch),
        )
    assert_never(stmt)


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


def rewrite_model_expr(
    expr: Expr,
    rewrite: Callable[[Expr], Expr],
) -> Expr:
    """Apply a local bottom-up rewrite across a model expression tree."""
    return _map_model_expr(expr, rewrite)


def replace_expr(expr: Expr, replacements: dict[Expr, str]) -> Expr:
    def fn(e: Expr) -> Expr:
        return Var(replacements[e]) if e in replacements else e

    return rewrite_model_expr(expr, fn)


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
        for_each_model_stmt(
            stmt,
            lambda current: _collect_binders_from_stmt(current, binders),
        )
    return binders


def _collect_binders_from_stmt(stmt: ModelStatement, out: list[str]) -> None:
    if isinstance(stmt, Assignment):
        out.append(stmt.target)
        return
    if isinstance(stmt, ConditionalBlock):
        out.extend(stmt.output_vars)
        return
    assert_never(stmt)
