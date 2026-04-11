from __future__ import annotations

from typing import Callable, assert_never

from evm_builtins import OP_TO_LEAN_HELPER, OP_TO_OPCODE
from model_ir import (
    Assignment,
    Call,
    ConditionalBlock,
    ConditionalBranch,
    Expr,
    FunctionModel,
    Ite,
    IntLit,
    ModelStatement,
    Project,
    Var,
)


def collect_ops(expr: Expr) -> list[str]:
    out: list[str] = []
    if isinstance(expr, Ite):
        out.extend(collect_ops(expr.cond))
        out.extend(collect_ops(expr.if_true))
        out.extend(collect_ops(expr.if_false))
    elif isinstance(expr, Project):
        out.extend(collect_ops(expr.inner))
    elif isinstance(expr, Call):
        if expr.name in OP_TO_OPCODE:
            out.append(expr.name)
        for arg in expr.args:
            out.extend(collect_ops(arg))
    return out


def _walk_model_exprs_in_stmt(
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


def _model_call_names_in_stmt(stmt: ModelStatement) -> set[str]:
    """Collect non-builtin call names from a model statement."""
    names: set[str] = set()

    def _walk(expr: Expr) -> None:
        if isinstance(expr, Call):
            if expr.name not in OP_TO_LEAN_HELPER:
                names.add(expr.name)
            for arg in expr.args:
                _walk(arg)
        elif isinstance(expr, Ite):
            _walk(expr.cond)
            _walk(expr.if_true)
            _walk(expr.if_false)
        elif isinstance(expr, Project):
            _walk(expr.inner)

    _walk_model_exprs_in_stmt(stmt, _walk)
    return names


def collect_ops_from_statement(stmt: ModelStatement) -> list[str]:
    """Collect opcodes from an Assignment or ConditionalBlock."""
    ops: list[str] = []
    _walk_model_exprs_in_stmt(stmt, lambda expr: ops.extend(collect_ops(expr)))
    return ops


def ordered_unique(items: list[str]) -> list[str]:
    d: dict[str, None] = dict.fromkeys(items)
    return list(d)


def collect_model_opcodes(models: list[FunctionModel]) -> list[str]:
    """Collect ordered unique opcodes used across all models."""
    raw_ops: list[str] = []
    for model in models:
        for stmt in model.assignments:
            raw_ops.extend(collect_ops_from_statement(stmt))
    return ordered_unique([OP_TO_OPCODE[name] for name in raw_ops])


def _expr_size(expr: Expr) -> int:
    if isinstance(expr, (IntLit, Var)):
        return 1
    if isinstance(expr, Ite):
        return (
            1
            + _expr_size(expr.cond)
            + _expr_size(expr.if_true)
            + _expr_size(expr.if_false)
        )
    if isinstance(expr, Project):
        return 1 + _expr_size(expr.inner)
    if isinstance(expr, Call):
        return 1 + sum(_expr_size(arg) for arg in expr.args)
    assert_never(expr)


def _replace_expr(expr: Expr, replacements: dict[Expr, str]) -> Expr:
    if expr in replacements:
        return Var(replacements[expr])
    if isinstance(expr, (IntLit, Var)):
        return expr
    if isinstance(expr, Ite):
        return Ite(
            _replace_expr(expr.cond, replacements),
            _replace_expr(expr.if_true, replacements),
            _replace_expr(expr.if_false, replacements),
        )
    if isinstance(expr, Project):
        return Project(expr.index, expr.total, _replace_expr(expr.inner, replacements))
    if isinstance(expr, Call):
        return Call(
            expr.name,
            tuple(_replace_expr(arg, replacements) for arg in expr.args),
            expr.binding_token_idx,
        )
    assert_never(expr)


def _expr_vars(expr: Expr) -> set[str]:
    if isinstance(expr, IntLit):
        return set()
    if isinstance(expr, Var):
        return {expr.name}
    if isinstance(expr, Ite):
        return (
            _expr_vars(expr.cond) | _expr_vars(expr.if_true) | _expr_vars(expr.if_false)
        )
    if isinstance(expr, Project):
        return _expr_vars(expr.inner)
    if isinstance(expr, Call):
        out: set[str] = set()
        for arg in expr.args:
            out.update(_expr_vars(arg))
        return out
    assert_never(expr)


def _walk_model_exprs_in_branch(
    branch: ConditionalBranch,
    visit: Callable[[Expr], None],
) -> None:
    for stmt in branch.assignments:
        _walk_model_exprs_in_stmt(stmt, visit)
    for expr in branch.outputs:
        visit(expr)


def _collect_model_binders(model: FunctionModel) -> list[str]:
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
