"""
Shared walker utilities for the Yul syntax AST.

Provides generic statement and expression traversals so that
consumer passes (selection) don't duplicate the full isinstance
dispatch over SynStmt/SynExpr variants.
"""

from __future__ import annotations

from collections.abc import Callable
from typing import TypeVar, assert_never, cast, overload

from .yul_ast import (
    AssignStmt,
    Block,
    BlockStmt,
    CallExpr,
    ExprStmt,
    ForStmt,
    FunctionDefStmt,
    IfStmt,
    IntExpr,
    LeaveStmt,
    LetStmt,
    NameExpr,
    StringExpr,
    SwitchStmt,
    SynExpr,
    SynStmt,
)

_T = TypeVar("_T")

# ---------------------------------------------------------------------------
# Expression visitor (pre-order)
# ---------------------------------------------------------------------------


def for_each_expr(expr: SynExpr, visit: Callable[[SynExpr], None]) -> None:
    """Call *visit* on every sub-expression in pre-order."""
    visit(expr)
    if isinstance(expr, (IntExpr, NameExpr, StringExpr)):
        pass
    elif isinstance(expr, CallExpr):
        for arg in expr.args:
            for_each_expr(arg, visit)
    else:
        assert_never(expr)


# ---------------------------------------------------------------------------
# Statement-level expression visitor
# ---------------------------------------------------------------------------


def for_each_expr_in_stmt(
    stmt: SynStmt,
    visit: Callable[[SynExpr], None],
) -> None:
    """Visit every direct expression slot on one statement.

    Recurses into sub-expressions of each slot via ``for_each_expr``.
    Does NOT recurse into sub-block statements.
    """
    if isinstance(stmt, LetStmt):
        if stmt.init is not None:
            for_each_expr(stmt.init, visit)
    elif isinstance(stmt, AssignStmt):
        for_each_expr(stmt.expr, visit)
    elif isinstance(stmt, ExprStmt):
        for_each_expr(stmt.expr, visit)
    elif isinstance(stmt, IfStmt):
        for_each_expr(stmt.condition, visit)
    elif isinstance(stmt, SwitchStmt):
        for_each_expr(stmt.discriminant, visit)
        for case in stmt.cases:
            for_each_expr(case.value, visit)
    elif isinstance(stmt, ForStmt):
        for_each_expr(stmt.condition, visit)
    elif isinstance(stmt, (LeaveStmt, BlockStmt, FunctionDefStmt)):
        pass
    else:
        assert_never(stmt)


# ---------------------------------------------------------------------------
# Block-level statement visitor (pre-order) with optional threaded context
# ---------------------------------------------------------------------------


@overload
def for_each_stmt_in_block(
    block: Block,
    visit: Callable[[SynStmt, None], None],
    ctx: None = None,
    *,
    include_function_bodies: bool = False,
) -> None: ...


@overload
def for_each_stmt_in_block(
    block: Block,
    visit: Callable[[SynStmt, _T], _T],
    ctx: _T,
    *,
    include_function_bodies: bool = False,
) -> None: ...


def for_each_stmt_in_block(
    block: Block,
    visit: Callable[[SynStmt, _T], _T],
    ctx: _T | None = None,
    *,
    include_function_bodies: bool = False,
) -> None:
    """Walk statements in pre-order with an optional threaded context.

    *visit* receives each statement and the current context, and
    returns a (possibly updated) context used when recursing into
    that statement's sub-blocks.  Sibling statements share the
    parent context, so updates inside one branch do not leak to
    the next.

    When no context is needed, pass a visitor that ignores and
    returns its second argument (or use the default *ctx* of
    ``None``).
    """

    def _walk(b: Block, parent_ctx: _T) -> None:
        for stmt in b.stmts:
            child_ctx = visit(stmt, parent_ctx)
            _recurse(stmt, child_ctx)

    def _recurse(stmt: SynStmt, c: _T) -> None:
        if isinstance(stmt, (LetStmt, AssignStmt, ExprStmt, LeaveStmt)):
            pass
        elif isinstance(stmt, BlockStmt):
            _walk(stmt.block, c)
        elif isinstance(stmt, IfStmt):
            _walk(stmt.body, c)
        elif isinstance(stmt, SwitchStmt):
            for case in stmt.cases:
                _walk(case.body, c)
            if stmt.default is not None:
                _walk(stmt.default.body, c)
        elif isinstance(stmt, ForStmt):
            _walk(stmt.init, c)
            _walk(stmt.post, c)
            _walk(stmt.body, c)
        elif isinstance(stmt, FunctionDefStmt):
            if include_function_bodies:
                _walk(stmt.func.body, c)
        else:
            assert_never(stmt)

    _walk(block, cast(_T, ctx))
