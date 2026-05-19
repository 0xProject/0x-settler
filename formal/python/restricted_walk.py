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

from .expr_walk import expr_contains as expr_contains
from .expr_walk import for_each_expr as for_each_expr
from .expr_walk import map_expr as map_expr
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
        for expr in stmt.then_branch.output_exprs:
            for_each_expr(expr, f)
        for expr in stmt.else_branch.output_exprs:
            for_each_expr(expr, f)
        return
    assert_never(stmt)
