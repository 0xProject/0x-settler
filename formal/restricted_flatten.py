"""
Control-flow flattening pass for restricted IR (pre-SSA).

Lifts nested ``RConditionalBlock`` nodes out of branch payloads,
converting them to flat sequences of assignments with ``RIte``
merges.

After this pass every ``RBranch.assignments`` contains only
``RAssignment`` and ``RCallAssign`` — no nested conditionals.

The transformation is semantics-preserving because the restricted
IR is pure: evaluating both sub-branches unconditionally and
selecting via ``RIte`` produces the same result as the branch-scoped
evaluation in the original IR.  Fresh ``SymbolId`` temporaries are
introduced so that then-branch writes do not clobber values needed
by else-branch output expressions.
"""

from __future__ import annotations

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
from yul_ast import SymbolId

# ---------------------------------------------------------------------------
# SymbolId allocator (local to this pass)
# ---------------------------------------------------------------------------


class _Alloc:
    def __init__(self, start: int) -> None:
        self._next = start

    def alloc(self) -> SymbolId:
        sid = SymbolId(self._next)
        self._next += 1
        return sid


def _max_sid_func(func: RestrictedFunction) -> int:
    """Find the maximum SymbolId._id in a RestrictedFunction."""
    ids: list[int] = [0]
    for sid in func.params:
        ids.append(sid._id)
    for sid in func.returns:
        ids.append(sid._id)
    for stmt in func.body:
        _collect_max_sid_stmt(stmt, ids)
    return max(ids)


def _collect_max_sid_stmt(stmt: RStatement, ids: list[int]) -> None:
    if isinstance(stmt, RAssignment):
        ids.append(stmt.target._id)
        _collect_max_sid_expr(stmt.expr, ids)
    elif isinstance(stmt, RCallAssign):
        for sid in stmt.targets:
            ids.append(sid._id)
        for a in stmt.args:
            _collect_max_sid_expr(a, ids)
    elif isinstance(stmt, RConditionalBlock):
        for sid in stmt.output_targets:
            ids.append(sid._id)
        _collect_max_sid_expr(stmt.condition, ids)
        for s in stmt.then_branch.assignments:
            _collect_max_sid_stmt(s, ids)
        for e in stmt.then_branch.output_exprs:
            _collect_max_sid_expr(e, ids)
        for s in stmt.else_branch.assignments:
            _collect_max_sid_stmt(s, ids)
        for e in stmt.else_branch.output_exprs:
            _collect_max_sid_expr(e, ids)


def _collect_max_sid_expr(expr: RExpr, ids: list[int]) -> None:
    if isinstance(expr, RRef):
        ids.append(expr.symbol_id._id)
    elif isinstance(expr, (RConst,)):
        pass
    elif isinstance(expr, (RBuiltinCall, RModelCall)):
        for a in expr.args:
            _collect_max_sid_expr(a, ids)
    elif isinstance(expr, RIte):
        _collect_max_sid_expr(expr.cond, ids)
        _collect_max_sid_expr(expr.if_true, ids)
        _collect_max_sid_expr(expr.if_false, ids)


# ---------------------------------------------------------------------------
# Expression / statement remapping
# ---------------------------------------------------------------------------

_Remap = dict[SymbolId, SymbolId]


def _remap_expr(expr: RExpr, remap: _Remap) -> RExpr:
    """Rewrite SymbolId references in *expr* according to *remap*."""
    if isinstance(expr, RConst):
        return expr
    if isinstance(expr, RRef):
        new_sid = remap.get(expr.symbol_id)
        if new_sid is None:
            return expr
        return RRef(symbol_id=new_sid, name=expr.name)
    if isinstance(expr, RBuiltinCall):
        return RBuiltinCall(
            op=expr.op,
            args=tuple(_remap_expr(a, remap) for a in expr.args),
        )
    if isinstance(expr, RModelCall):
        return RModelCall(
            name=expr.name,
            args=tuple(_remap_expr(a, remap) for a in expr.args),
        )
    if isinstance(expr, RIte):
        return RIte(
            cond=_remap_expr(expr.cond, remap),
            if_true=_remap_expr(expr.if_true, remap),
            if_false=_remap_expr(expr.if_false, remap),
        )
    raise ValueError(f"Unexpected RExpr: {type(expr).__name__}")


def _remap_stmt(stmt: RStatement, remap: _Remap) -> RStatement:
    """Rewrite SymbolId references in *stmt* according to *remap*.

    Only references are remapped, not assignment targets.
    """
    if isinstance(stmt, RAssignment):
        return RAssignment(
            target=stmt.target,
            target_name=stmt.target_name,
            expr=_remap_expr(stmt.expr, remap),
        )
    if isinstance(stmt, RCallAssign):
        return RCallAssign(
            targets=stmt.targets,
            target_names=stmt.target_names,
            callee=stmt.callee,
            args=tuple(_remap_expr(a, remap) for a in stmt.args),
        )
    if isinstance(stmt, RConditionalBlock):
        return RConditionalBlock(
            condition=_remap_expr(stmt.condition, remap),
            output_targets=stmt.output_targets,
            output_names=stmt.output_names,
            then_branch=RBranch(
                assignments=tuple(
                    _remap_stmt(s, remap) for s in stmt.then_branch.assignments
                ),
                output_exprs=tuple(
                    _remap_expr(e, remap) for e in stmt.then_branch.output_exprs
                ),
            ),
            else_branch=RBranch(
                assignments=tuple(
                    _remap_stmt(s, remap) for s in stmt.else_branch.assignments
                ),
                output_exprs=tuple(
                    _remap_expr(e, remap) for e in stmt.else_branch.output_exprs
                ),
            ),
        )
    raise ValueError(f"Unexpected RStatement: {type(stmt).__name__}")


# ---------------------------------------------------------------------------
# Branch flattening core
# ---------------------------------------------------------------------------


def _emit_branch_flat(
    stmts: tuple[RStatement, ...],
    alloc: _Alloc,
    out: list[RStatement],
) -> _Remap:
    """Emit branch-local statements as flat assignments with fresh targets.

    Each assignment target is replaced by a fresh ``SymbolId`` so that
    writes in one sub-branch cannot clobber values needed by the other.
    Returns a remap from original targets to their fresh versions.
    """
    remap: _Remap = {}
    for stmt in stmts:
        if isinstance(stmt, RAssignment):
            expr = _remap_expr(stmt.expr, remap)
            fresh = alloc.alloc()
            remap[stmt.target] = fresh
            out.append(
                RAssignment(target=fresh, target_name=stmt.target_name, expr=expr)
            )
        elif isinstance(stmt, RCallAssign):
            args = tuple(_remap_expr(a, remap) for a in stmt.args)
            fresh_targets: list[SymbolId] = []
            for sid in stmt.targets:
                fresh = alloc.alloc()
                remap[sid] = fresh
                fresh_targets.append(fresh)
            out.append(
                RCallAssign(
                    targets=tuple(fresh_targets),
                    target_names=stmt.target_names,
                    callee=stmt.callee,
                    args=args,
                )
            )
        elif isinstance(stmt, RConditionalBlock):
            # Recursive: flatten the nested conditional.
            # First remap its references to use the current branch state.
            remapped_cond = _remap_stmt(stmt, remap)
            assert isinstance(remapped_cond, RConditionalBlock)
            _flatten_nested_conditional(
                remapped_cond, stmt.output_targets, remap, alloc, out
            )
        else:
            raise ValueError(f"Unexpected RStatement: {type(stmt).__name__}")
    return remap


def _flatten_nested_conditional(
    cond: RConditionalBlock,
    original_output_targets: tuple[SymbolId, ...],
    outer_remap: _Remap,
    alloc: _Alloc,
    out: list[RStatement],
) -> None:
    """Convert a nested conditional to flat assignments with ``RIte`` merges.

    Emits both sub-branches' assignments (with fresh targets) followed
    by one ``RIte`` merge assignment per output target.  Updates
    *outer_remap* so subsequent statements in the enclosing branch
    see the merged values.
    """
    # Process then-branch with fresh SymbolIds.
    then_remap = _emit_branch_flat(cond.then_branch.assignments, alloc, out)

    # Process else-branch with fresh SymbolIds.
    else_remap = _emit_branch_flat(cond.else_branch.assignments, alloc, out)

    # Emit RIte merges.
    for orig_sid, out_name, then_expr, else_expr in zip(
        original_output_targets,
        cond.output_names,
        cond.then_branch.output_exprs,
        cond.else_branch.output_exprs,
    ):
        remapped_then = _remap_expr(then_expr, then_remap)
        remapped_else = _remap_expr(else_expr, else_remap)
        fresh = alloc.alloc()
        outer_remap[orig_sid] = fresh
        out.append(
            RAssignment(
                target=fresh,
                target_name=out_name,
                expr=RIte(cond.condition, remapped_then, remapped_else),
            )
        )


# ---------------------------------------------------------------------------
# Top-level flattening
# ---------------------------------------------------------------------------


def _flatten_top_stmts(
    stmts: tuple[RStatement, ...], alloc: _Alloc
) -> list[RStatement]:
    """Process top-level statements: keep conditionals but flatten branches."""
    out: list[RStatement] = []
    for stmt in stmts:
        if isinstance(stmt, RConditionalBlock):
            out.append(_flatten_top_conditional(stmt, alloc))
        else:
            out.append(stmt)
    return out


def _flatten_top_conditional(
    cond: RConditionalBlock, alloc: _Alloc
) -> RConditionalBlock:
    """Flatten a top-level conditional: ensure branches are flat."""
    return RConditionalBlock(
        condition=cond.condition,
        output_targets=cond.output_targets,
        output_names=cond.output_names,
        then_branch=_flatten_branch(cond.then_branch, alloc),
        else_branch=_flatten_branch(cond.else_branch, alloc),
    )


def _flatten_branch(branch: RBranch, alloc: _Alloc) -> RBranch:
    """Flatten a branch: convert nested conditionals to ``RIte`` assignments."""
    has_nested = any(isinstance(s, RConditionalBlock) for s in branch.assignments)
    if not has_nested:
        return branch

    flat: list[RStatement] = []
    remap = _emit_branch_flat(branch.assignments, alloc, flat)

    new_outputs = tuple(_remap_expr(e, remap) for e in branch.output_exprs)
    return RBranch(assignments=tuple(flat), output_exprs=new_outputs)


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def flatten_function(func: RestrictedFunction) -> RestrictedFunction:
    """Flatten nested conditionals in all branch bodies.

    After this pass, every ``RBranch.assignments`` contains only
    ``RAssignment`` and ``RCallAssign``.
    """
    alloc = _Alloc(_max_sid_func(func) + 1)
    new_body = _flatten_top_stmts(func.body, alloc)
    return RestrictedFunction(
        name=func.name,
        params=func.params,
        param_names=func.param_names,
        returns=func.returns,
        return_names=func.return_names,
        body=tuple(new_body),
    )
