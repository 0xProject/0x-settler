"""
Shared walker utilities for the restricted IR.

Provides generic expression and statement traversals so that
consumer passes (name_policy, restricted_to_model, restricted_eval)
don't each duplicate the full isinstance dispatch over
RExpr/RStatement variants.
"""

from __future__ import annotations

from collections.abc import Callable
from typing import assert_never

from .restricted_ir import (
    RAssignment,
    RBranch,
    RBuiltinCall,
    RCallAssign,
    RConditionalBlock,
    RConst,
    RExpr,
    RIte,
    RModelCall,
    RRef,
    RStatement,
)
from .yul_ast import SymbolId

# ---------------------------------------------------------------------------
# Expression mapper (bottom-up)
# ---------------------------------------------------------------------------


def map_expr(expr: RExpr, f: Callable[[RExpr], RExpr]) -> RExpr:
    """Apply *f* bottom-up to every node in the expression tree.

    Children are mapped first, then *f* is called on the
    reconstructed parent.
    """
    if isinstance(expr, (RConst, RRef)):
        return f(expr)

    if isinstance(expr, RBuiltinCall):
        mapped_args = tuple(map_expr(a, f) for a in expr.args)
        return f(RBuiltinCall(op=expr.op, args=mapped_args))

    if isinstance(expr, RModelCall):
        mapped_args = tuple(map_expr(a, f) for a in expr.args)
        return f(RModelCall(name=expr.name, args=mapped_args))

    if isinstance(expr, RIte):
        return f(
            RIte(
                cond=map_expr(expr.cond, f),
                if_true=map_expr(expr.if_true, f),
                if_false=map_expr(expr.if_false, f),
            )
        )

    assert_never(expr)


# ---------------------------------------------------------------------------
# Expression visitor (pre-order)
# ---------------------------------------------------------------------------


def for_each_expr(expr: RExpr, f: Callable[[RExpr], None]) -> None:
    """Call *f* on every sub-expression in pre-order."""
    f(expr)
    if isinstance(expr, (RConst, RRef)):
        pass
    elif isinstance(expr, (RBuiltinCall, RModelCall)):
        for a in expr.args:
            for_each_expr(a, f)
    elif isinstance(expr, RIte):
        for_each_expr(expr.cond, f)
        for_each_expr(expr.if_true, f)
        for_each_expr(expr.if_false, f)
    else:
        assert_never(expr)


def expr_contains(expr: RExpr, predicate: Callable[[RExpr], bool]) -> bool:
    """Return whether any sub-expression satisfies *predicate*."""
    if predicate(expr):
        return True
    if isinstance(expr, (RConst, RRef)):
        return False
    if isinstance(expr, (RBuiltinCall, RModelCall)):
        return any(expr_contains(a, predicate) for a in expr.args)
    if isinstance(expr, RIte):
        return (
            expr_contains(expr.cond, predicate)
            or expr_contains(expr.if_true, predicate)
            or expr_contains(expr.if_false, predicate)
        )
    assert_never(expr)


# ---------------------------------------------------------------------------
# Statement mapper
# ---------------------------------------------------------------------------


def map_stmt(
    stmt: RStatement,
    *,
    map_expr_fn: Callable[[RExpr], RExpr],
    map_branch_fn: (
        Callable[[tuple[RStatement, ...]], tuple[RStatement, ...]] | None
    ) = None,
    map_target_name: Callable[[SymbolId, str], str] | None = None,
    map_callee: Callable[[str], str] | None = None,
) -> RStatement:
    """Map expressions and recurse into sub-statements structurally.

    *map_target_name* (optional) remaps assignment target names.
    *map_callee* (optional) remaps call-assign callee names.
    *map_branch_fn* (optional) remaps branch assignment tuples;
    when *None*, each statement in the branch is mapped with the
    same callbacks.
    """

    def _default_branch(stmts: tuple[RStatement, ...]) -> tuple[RStatement, ...]:
        return tuple(
            map_stmt(
                s,
                map_expr_fn=map_expr_fn,
                map_branch_fn=map_branch_fn,
                map_target_name=map_target_name,
                map_callee=map_callee,
            )
            for s in stmts
        )

    branch_fn = map_branch_fn if map_branch_fn is not None else _default_branch

    def _tgt(sid: SymbolId, name: str) -> str:
        return map_target_name(sid, name) if map_target_name else name

    def _callee(name: str) -> str:
        return map_callee(name) if map_callee else name

    if isinstance(stmt, RAssignment):
        return RAssignment(
            target=stmt.target,
            target_name=_tgt(stmt.target, stmt.target_name),
            expr=map_expr_fn(stmt.expr),
        )

    if isinstance(stmt, RCallAssign):
        return RCallAssign(
            targets=stmt.targets,
            target_names=tuple(
                _tgt(sid, name) for sid, name in zip(stmt.targets, stmt.target_names)
            ),
            callee=_callee(stmt.callee),
            args=tuple(map_expr_fn(arg) for arg in stmt.args),
        )

    if isinstance(stmt, RConditionalBlock):
        return RConditionalBlock(
            condition=map_expr_fn(stmt.condition),
            output_targets=stmt.output_targets,
            output_names=tuple(
                _tgt(sid, name)
                for sid, name in zip(stmt.output_targets, stmt.output_names)
            ),
            then_branch=RBranch(
                assignments=branch_fn(stmt.then_branch.assignments),
                output_exprs=tuple(
                    map_expr_fn(expr) for expr in stmt.then_branch.output_exprs
                ),
            ),
            else_branch=RBranch(
                assignments=branch_fn(stmt.else_branch.assignments),
                output_exprs=tuple(
                    map_expr_fn(expr) for expr in stmt.else_branch.output_exprs
                ),
            ),
        )

    assert_never(stmt)


# ---------------------------------------------------------------------------
# Statement visitor (pre-order)
# ---------------------------------------------------------------------------


def for_each_stmt(
    stmts: tuple[RStatement, ...],
    f: Callable[[RStatement], None],
) -> None:
    """Call *f* on every statement in pre-order, recursing into branches."""
    for stmt in stmts:
        f(stmt)
        if isinstance(stmt, (RAssignment, RCallAssign)):
            pass
        elif isinstance(stmt, RConditionalBlock):
            for_each_stmt(stmt.then_branch.assignments, f)
            for_each_stmt(stmt.else_branch.assignments, f)
        else:
            assert_never(stmt)


def for_each_stmt_expr(stmt: RStatement, f: Callable[[RExpr], None]) -> None:
    """Visit every direct expression slot carried by one statement."""
    if isinstance(stmt, RAssignment):
        for_each_expr(stmt.expr, f)
        return
    if isinstance(stmt, RCallAssign):
        for arg in stmt.args:
            for_each_expr(arg, f)
        return
    if isinstance(stmt, RConditionalBlock):
        for_each_expr(stmt.condition, f)
        return
    assert_never(stmt)
