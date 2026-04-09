"""
Pure helper inlining on the normalized imperative IR.

Replaces ``NLocalCall`` nodes to pure helpers (no memory, no leave,
no for-loops) with the helper's body evaluated as a symbolic
expression.  This is the normalized-IR equivalent of the old
pipeline's ``_inline_single_call()`` + ``inline_calls()``.
"""

from __future__ import annotations

from typing import assert_never

from norm_classify import InlineClassification, classify_function_scope
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
    NIte,
    NLeave,
    NLocalCall,
    NormalizedFunction,
    NRef,
    NStmt,
    NSwitch,
    NTopLevelCall,
    NUnresolvedCall,
)
from yul_ast import ParseError, SymbolId

# ---------------------------------------------------------------------------
# SymbolId allocator
# ---------------------------------------------------------------------------


class SymbolAllocator:
    """Generates fresh ``SymbolId`` values for alpha-renaming."""

    def __init__(self, start: int) -> None:
        self._next = start

    def alloc(self) -> SymbolId:
        sid = SymbolId(self._next)
        self._next += 1
        return sid


def _max_symbol_id_impl(func: NormalizedFunction) -> int:
    """Find the maximum SymbolId._id in a function."""
    result: list[int] = [0]
    for sid in func.params:
        if sid._id > result[0]:
            result[0] = sid._id
    for sid in func.returns:
        if sid._id > result[0]:
            result[0] = sid._id
    _scan_block_ids(func.body, result)
    return result[0]


def _scan_block_ids(block: NBlock, result: list[int]) -> None:
    for stmt in block.stmts:
        _scan_stmt_ids(stmt, result)


def _scan_stmt_ids(stmt: NStmt, result: list[int]) -> None:
    if isinstance(stmt, NBind):
        for sid in stmt.targets:
            if sid._id > result[0]:
                result[0] = sid._id
        if stmt.expr is not None:
            _scan_expr_ids(stmt.expr, result)
    elif isinstance(stmt, NAssign):
        for sid in stmt.targets:
            if sid._id > result[0]:
                result[0] = sid._id
        _scan_expr_ids(stmt.expr, result)
    elif isinstance(stmt, NExprEffect):
        _scan_expr_ids(stmt.expr, result)
    elif isinstance(stmt, NIf):
        _scan_expr_ids(stmt.condition, result)
        _scan_block_ids(stmt.then_body, result)
    elif isinstance(stmt, NSwitch):
        _scan_expr_ids(stmt.discriminant, result)
        for case in stmt.cases:
            _scan_block_ids(case.body, result)
        if stmt.default is not None:
            _scan_block_ids(stmt.default, result)
    elif isinstance(stmt, NFor):
        _scan_block_ids(stmt.init, result)
        _scan_expr_ids(stmt.condition, result)
        _scan_block_ids(stmt.post, result)
        _scan_block_ids(stmt.body, result)
    elif isinstance(stmt, NLeave):
        pass
    elif isinstance(stmt, NBlock):
        _scan_block_ids(stmt, result)
    elif isinstance(stmt, NFunctionDef):
        if stmt.symbol_id._id > result[0]:
            result[0] = stmt.symbol_id._id
        for sid in stmt.params:
            if sid._id > result[0]:
                result[0] = sid._id
        for sid in stmt.returns:
            if sid._id > result[0]:
                result[0] = sid._id
        _scan_block_ids(stmt.body, result)


def _scan_expr_ids(expr: NExpr, result: list[int]) -> None:
    if isinstance(expr, NConst):
        pass
    elif isinstance(expr, NRef):
        if expr.symbol_id._id > result[0]:
            result[0] = expr.symbol_id._id
    elif isinstance(expr, NBuiltinCall):
        for a in expr.args:
            _scan_expr_ids(a, result)
    elif isinstance(expr, NLocalCall):
        if expr.symbol_id._id > result[0]:
            result[0] = expr.symbol_id._id
        for a in expr.args:
            _scan_expr_ids(a, result)
    elif isinstance(expr, (NTopLevelCall, NUnresolvedCall)):
        for a in expr.args:
            _scan_expr_ids(a, result)
    elif isinstance(expr, NIte):
        _scan_expr_ids(expr.cond, result)
        _scan_expr_ids(expr.if_true, result)
        _scan_expr_ids(expr.if_false, result)


# ---------------------------------------------------------------------------
# Expression substitution
# ---------------------------------------------------------------------------


def substitute_nexpr(
    expr: NExpr,
    subst: dict[SymbolId, NExpr],
) -> NExpr:
    """Replace ``NRef`` nodes according to *subst*."""
    if isinstance(expr, NConst):
        return expr
    if isinstance(expr, NRef):
        return subst.get(expr.symbol_id, expr)
    if isinstance(expr, NBuiltinCall):
        return NBuiltinCall(
            op=expr.op,
            args=tuple(substitute_nexpr(a, subst) for a in expr.args),
        )
    if isinstance(expr, NLocalCall):
        return NLocalCall(
            symbol_id=expr.symbol_id,
            name=expr.name,
            args=tuple(substitute_nexpr(a, subst) for a in expr.args),
        )
    if isinstance(expr, NTopLevelCall):
        return NTopLevelCall(
            name=expr.name,
            args=tuple(substitute_nexpr(a, subst) for a in expr.args),
        )
    if isinstance(expr, NUnresolvedCall):
        return NUnresolvedCall(
            name=expr.name,
            args=tuple(substitute_nexpr(a, subst) for a in expr.args),
        )
    if isinstance(expr, NIte):
        return NIte(
            cond=substitute_nexpr(expr.cond, subst),
            if_true=substitute_nexpr(expr.if_true, subst),
            if_false=substitute_nexpr(expr.if_false, subst),
        )
    assert_never(expr)


# ---------------------------------------------------------------------------
# Collect referenced SymbolIds in an expression
# ---------------------------------------------------------------------------


def _collect_refs(expr: NExpr, out: set[SymbolId]) -> None:
    if isinstance(expr, NConst):
        pass
    elif isinstance(expr, NRef):
        out.add(expr.symbol_id)
    elif isinstance(expr, NBuiltinCall):
        for a in expr.args:
            _collect_refs(a, out)
    elif isinstance(expr, NLocalCall):
        for a in expr.args:
            _collect_refs(a, out)
    elif isinstance(expr, (NTopLevelCall, NUnresolvedCall)):
        for a in expr.args:
            _collect_refs(a, out)
    elif isinstance(expr, NIte):
        _collect_refs(expr.cond, out)
        _collect_refs(expr.if_true, out)
        _collect_refs(expr.if_false, out)


# ---------------------------------------------------------------------------
# Simplify Ite
# ---------------------------------------------------------------------------


def _try_const(expr: NExpr) -> int | None:
    """Return the integer value if *expr* is a constant, else None."""
    if isinstance(expr, NConst):
        return expr.value
    return None


def _simplify_ite(cond: NExpr, if_true: NExpr, if_false: NExpr) -> NExpr:
    """Build an ``NIte``, simplifying trivial cases."""
    if if_true == if_false:
        return if_true
    c = _try_const(cond)
    if c is not None:
        return if_true if c != 0 else if_false
    return NIte(cond=cond, if_true=if_true, if_false=if_false)


# ---------------------------------------------------------------------------
# Alpha-renaming
# ---------------------------------------------------------------------------


def _collect_callee_locals(fdef: NFunctionDef) -> set[SymbolId]:
    """Collect SymbolIds declared in the helper body (not params/returns)."""
    param_ret: set[SymbolId] = set(fdef.params) | set(fdef.returns)
    locals_: set[SymbolId] = set()
    _collect_locals_in_block(fdef.body, param_ret, locals_)
    return locals_


def _collect_locals_in_block(
    block: NBlock, exclude: set[SymbolId], out: set[SymbolId]
) -> None:
    for stmt in block.stmts:
        if isinstance(stmt, NBind):
            for sid in stmt.targets:
                if sid not in exclude:
                    out.add(sid)
        elif isinstance(stmt, NIf):
            _collect_locals_in_block(stmt.then_body, exclude, out)
        elif isinstance(stmt, NBlock):
            _collect_locals_in_block(stmt, exclude, out)


def _alpha_rename_if_needed(
    fdef: NFunctionDef,
    args: tuple[NExpr, ...],
    alloc: SymbolAllocator,
) -> NFunctionDef:
    """Alpha-rename callee locals that collide with argument variable refs."""
    arg_refs: set[SymbolId] = set()
    for a in args:
        _collect_refs(a, arg_refs)

    callee_locals = _collect_callee_locals(fdef)
    collisions = callee_locals & arg_refs
    if not collisions:
        return fdef

    rename_map: dict[SymbolId, NExpr] = {}
    for old_sid in collisions:
        new_sid = alloc.alloc()
        rename_map[old_sid] = NRef(symbol_id=new_sid, name=f"_inl_{old_sid._id}")

    # Rewrite the body with the rename map.
    new_body = _substitute_block(fdef.body, rename_map)

    # Update target lists in NBind statements.
    sid_map: dict[SymbolId, SymbolId] = {}
    for old_sid, new_ref in rename_map.items():
        assert isinstance(new_ref, NRef)
        sid_map[old_sid] = new_ref.symbol_id

    new_body = _remap_bind_targets(new_body, sid_map)

    return NFunctionDef(
        name=fdef.name,
        symbol_id=fdef.symbol_id,
        params=fdef.params,
        param_names=fdef.param_names,
        returns=fdef.returns,
        return_names=fdef.return_names,
        body=new_body,
    )


def _substitute_block(block: NBlock, subst: dict[SymbolId, NExpr]) -> NBlock:
    return NBlock(tuple(_substitute_stmt(s, subst) for s in block.stmts))


def _substitute_stmt(stmt: NStmt, subst: dict[SymbolId, NExpr]) -> NStmt:
    if isinstance(stmt, NBind):
        return NBind(
            targets=stmt.targets,
            target_names=stmt.target_names,
            expr=substitute_nexpr(stmt.expr, subst) if stmt.expr is not None else None,
        )
    if isinstance(stmt, NAssign):
        return NAssign(
            targets=stmt.targets,
            target_names=stmt.target_names,
            expr=substitute_nexpr(stmt.expr, subst),
        )
    if isinstance(stmt, NIf):
        return NIf(
            condition=substitute_nexpr(stmt.condition, subst),
            then_body=_substitute_block(stmt.then_body, subst),
        )
    if isinstance(stmt, NBlock):
        return _substitute_block(stmt, subst)
    if isinstance(stmt, NFunctionDef):
        return stmt  # Don't descend into nested function bodies
    if isinstance(stmt, NExprEffect):
        return NExprEffect(expr=substitute_nexpr(stmt.expr, subst))
    if isinstance(stmt, (NFor, NLeave, NSwitch)):
        return stmt  # Should not appear in pure helpers
    assert_never(stmt)


def _remap_bind_targets(block: NBlock, sid_map: dict[SymbolId, SymbolId]) -> NBlock:
    """Remap SymbolIds in NBind/NAssign targets."""
    return NBlock(tuple(_remap_stmt_targets(s, sid_map) for s in block.stmts))


def _remap_stmt_targets(stmt: NStmt, sid_map: dict[SymbolId, SymbolId]) -> NStmt:
    if isinstance(stmt, NBind):
        new_targets = tuple(sid_map.get(s, s) for s in stmt.targets)
        new_names = tuple(
            f"_inl_{s._id}" if s in sid_map else n
            for s, n in zip(stmt.targets, stmt.target_names)
        )
        return NBind(targets=new_targets, target_names=new_names, expr=stmt.expr)
    if isinstance(stmt, NAssign):
        new_targets = tuple(sid_map.get(s, s) for s in stmt.targets)
        new_names = tuple(
            f"_inl_{s._id}" if s in sid_map else n
            for s, n in zip(stmt.targets, stmt.target_names)
        )
        return NAssign(targets=new_targets, target_names=new_names, expr=stmt.expr)
    if isinstance(stmt, NIf):
        return NIf(
            condition=stmt.condition,
            then_body=_remap_bind_targets(stmt.then_body, sid_map),
        )
    if isinstance(stmt, NBlock):
        return _remap_bind_targets(stmt, sid_map)
    return stmt


# ---------------------------------------------------------------------------
# Single-call inlining (pure helpers only)
# ---------------------------------------------------------------------------

_InlineResult = NExpr | tuple[NExpr, ...]


def inline_pure_call(
    fdef: NFunctionDef,
    args: tuple[NExpr, ...],
    alloc: SymbolAllocator,
    classifications: dict[SymbolId, InlineClassification],
    local_funcs: dict[SymbolId, NFunctionDef],
    *,
    depth: int = 0,
    max_depth: int = 40,
) -> _InlineResult:
    """Inline a single pure helper call, returning its return expression(s).

    Pure helpers have no memory effects, no leave, no for-loops.
    """
    if depth > max_depth:
        raise ParseError(
            f"Inlining depth limit ({max_depth}) exceeded for {fdef.name!r}"
        )

    fdef = _alpha_rename_if_needed(fdef, args, alloc)

    # Seed substitution: params → args, returns → 0.
    subst: dict[SymbolId, NExpr] = {}
    for sid, arg in zip(fdef.params, args):
        subst[sid] = arg
    for sid in fdef.returns:
        subst[sid] = NConst(0)

    # Process body statements.
    _process_pure_block(
        fdef.body, subst, alloc, classifications, local_funcs, depth, max_depth
    )

    # Extract return values.
    if len(fdef.returns) == 1:
        return subst[fdef.returns[0]]
    return tuple(subst[sid] for sid in fdef.returns)


def _process_pure_block(
    block: NBlock,
    subst: dict[SymbolId, NExpr],
    alloc: SymbolAllocator,
    classifications: dict[SymbolId, InlineClassification],
    local_funcs: dict[SymbolId, NFunctionDef],
    depth: int,
    max_depth: int,
) -> None:
    """Process a block's statements, updating *subst* in place."""
    for stmt in block.stmts:
        _process_pure_stmt(
            stmt, subst, alloc, classifications, local_funcs, depth, max_depth
        )


def _process_pure_stmt(
    stmt: NStmt,
    subst: dict[SymbolId, NExpr],
    alloc: SymbolAllocator,
    classifications: dict[SymbolId, InlineClassification],
    local_funcs: dict[SymbolId, NFunctionDef],
    depth: int,
    max_depth: int,
) -> None:
    if isinstance(stmt, (NBind, NAssign)):
        if stmt.expr is not None:
            expr = substitute_nexpr(stmt.expr, subst)
            expr = _inline_in_expr(
                expr, alloc, classifications, local_funcs, depth, max_depth
            )
            if len(stmt.targets) == 1:
                subst[stmt.targets[0]] = expr
            else:
                # Multi-target: expr must be a tuple (multi-return call result).
                # This shouldn't happen after inlining (calls are replaced), but
                # handle it defensively.
                subst[stmt.targets[0]] = expr
        else:
            # Bare let — initialize to 0.
            for sid in stmt.targets:
                subst[sid] = NConst(0)
        return

    if isinstance(stmt, NIf):
        cond = substitute_nexpr(stmt.condition, subst)
        cond = _inline_in_expr(
            cond, alloc, classifications, local_funcs, depth, max_depth
        )

        # Try constant folding.
        c = _try_const(cond)
        if c is not None:
            if c != 0:
                _process_pure_block(
                    stmt.then_body,
                    subst,
                    alloc,
                    classifications,
                    local_funcs,
                    depth,
                    max_depth,
                )
            # else: dead branch, skip
            return

        # Non-constant: process then-branch with separate subst, merge with NIte.
        if_subst = dict(subst)
        _process_pure_block(
            stmt.then_body,
            if_subst,
            alloc,
            classifications,
            local_funcs,
            depth,
            max_depth,
        )
        # Merge: for each modified variable, create NIte.
        for sid in if_subst:
            if if_subst[sid] is not subst.get(sid):
                pre_val = subst.get(sid, NConst(0))
                if_val = if_subst[sid]
                subst[sid] = _simplify_ite(cond, if_val, pre_val)
        return

    if isinstance(stmt, NFunctionDef):
        # Structural; not executed. But register in local_funcs for
        # nested call resolution.
        local_funcs[stmt.symbol_id] = stmt
        return

    if isinstance(stmt, NBlock):
        _process_pure_block(
            stmt, subst, alloc, classifications, local_funcs, depth, max_depth
        )
        return

    if isinstance(stmt, (NFor, NLeave, NExprEffect, NSwitch)):
        raise ParseError(f"Unexpected {type(stmt).__name__} in pure helper body")

    assert_never(stmt)


# ---------------------------------------------------------------------------
# Inline calls within expressions
# ---------------------------------------------------------------------------


def _inline_in_expr(
    expr: NExpr,
    alloc: SymbolAllocator,
    classifications: dict[SymbolId, InlineClassification],
    local_funcs: dict[SymbolId, NFunctionDef],
    depth: int,
    max_depth: int,
) -> NExpr:
    """Recursively inline pure helper calls within an expression."""
    if isinstance(expr, (NConst, NRef)):
        return expr

    if isinstance(expr, NBuiltinCall):
        new_args = tuple(
            _inline_in_expr(a, alloc, classifications, local_funcs, depth, max_depth)
            for a in expr.args
        )
        return NBuiltinCall(op=expr.op, args=new_args)

    if isinstance(expr, NLocalCall):
        new_args = tuple(
            _inline_in_expr(a, alloc, classifications, local_funcs, depth, max_depth)
            for a in expr.args
        )
        # Can we inline this call?
        cls = classifications.get(expr.symbol_id)
        if cls is not None and cls.is_pure and expr.symbol_id in local_funcs:
            fdef = local_funcs[expr.symbol_id]
            result = inline_pure_call(
                fdef,
                new_args,
                alloc,
                classifications,
                local_funcs,
                depth=depth + 1,
                max_depth=max_depth,
            )
            if isinstance(result, tuple):
                raise ParseError(
                    f"Multi-return call to {expr.name!r} in single-value context"
                )
            return result
        return NLocalCall(symbol_id=expr.symbol_id, name=expr.name, args=new_args)

    if isinstance(expr, (NTopLevelCall, NUnresolvedCall)):
        new_args = tuple(
            _inline_in_expr(a, alloc, classifications, local_funcs, depth, max_depth)
            for a in expr.args
        )
        if isinstance(expr, NTopLevelCall):
            return NTopLevelCall(name=expr.name, args=new_args)
        return NUnresolvedCall(name=expr.name, args=new_args)

    if isinstance(expr, NIte):
        return NIte(
            cond=_inline_in_expr(
                expr.cond, alloc, classifications, local_funcs, depth, max_depth
            ),
            if_true=_inline_in_expr(
                expr.if_true, alloc, classifications, local_funcs, depth, max_depth
            ),
            if_false=_inline_in_expr(
                expr.if_false, alloc, classifications, local_funcs, depth, max_depth
            ),
        )

    assert_never(expr)


# ---------------------------------------------------------------------------
# Public API: inline all pure helpers in a function
# ---------------------------------------------------------------------------


def inline_pure_helpers(
    func: NormalizedFunction,
) -> NormalizedFunction:
    """Inline all pure helper calls in *func*.

    Classifies nested helpers, then walks the body replacing
    ``NLocalCall`` to pure helpers with their inlined expressions.
    """
    classifications = classify_function_scope(func)
    alloc = SymbolAllocator(_max_symbol_id_impl(func) + 1)

    # Collect all local function defs.
    local_funcs: dict[SymbolId, NFunctionDef] = {}
    _collect_all_fdefs(func.body, local_funcs)

    # Inline expressions in the body.
    new_stmts = _inline_block_stmts(func.body, alloc, classifications, local_funcs)

    return NormalizedFunction(
        name=func.name,
        params=func.params,
        param_names=func.param_names,
        returns=func.returns,
        return_names=func.return_names,
        body=NBlock(tuple(new_stmts)),
    )


def _collect_all_fdefs(block: NBlock, out: dict[SymbolId, NFunctionDef]) -> None:
    for stmt in block.stmts:
        if isinstance(stmt, NFunctionDef):
            out[stmt.symbol_id] = stmt
            _collect_all_fdefs(stmt.body, out)
        elif isinstance(stmt, NIf):
            _collect_all_fdefs(stmt.then_body, out)
        elif isinstance(stmt, NSwitch):
            for case in stmt.cases:
                _collect_all_fdefs(case.body, out)
            if stmt.default is not None:
                _collect_all_fdefs(stmt.default, out)
        elif isinstance(stmt, NFor):
            _collect_all_fdefs(stmt.init, out)
            _collect_all_fdefs(stmt.post, out)
            _collect_all_fdefs(stmt.body, out)
        elif isinstance(stmt, NBlock):
            _collect_all_fdefs(stmt, out)


def _inline_block_stmts(
    block: NBlock,
    alloc: SymbolAllocator,
    classifications: dict[SymbolId, InlineClassification],
    local_funcs: dict[SymbolId, NFunctionDef],
) -> list[NStmt]:
    """Inline pure calls in a block's statements (top-level body walk)."""
    result: list[NStmt] = []
    for stmt in block.stmts:
        if isinstance(stmt, (NBind, NAssign)):
            expr = stmt.expr

            # Multi-target with pure NLocalCall: handle BEFORE general
            # _inline_in_expr (which would reject multi-return in
            # single-value expression context).
            if (
                expr is not None
                and len(stmt.targets) > 1
                and isinstance(expr, NLocalCall)
                and _is_inlineable(expr.symbol_id, classifications, local_funcs)
            ):
                fdef = local_funcs[expr.symbol_id]
                # Inline arguments first.
                new_args = tuple(
                    _inline_in_expr(a, alloc, classifications, local_funcs, 0, 40)
                    for a in expr.args
                )
                inlined = inline_pure_call(
                    fdef, new_args, alloc, classifications, local_funcs
                )
                if isinstance(inlined, tuple) and len(inlined) == len(stmt.targets):
                    cls = NBind if isinstance(stmt, NBind) else NAssign
                    for sid, name, val in zip(stmt.targets, stmt.target_names, inlined):
                        result.append(
                            cls(targets=(sid,), target_names=(name,), expr=val)
                        )
                    continue

            # General case: inline within expression.
            if expr is not None:
                expr = _inline_in_expr(expr, alloc, classifications, local_funcs, 0, 40)
            if isinstance(stmt, NBind):
                result.append(
                    NBind(
                        targets=stmt.targets,
                        target_names=stmt.target_names,
                        expr=expr,
                    )
                )
            else:
                assert isinstance(stmt, NAssign)
                assert expr is not None
                result.append(
                    NAssign(
                        targets=stmt.targets,
                        target_names=stmt.target_names,
                        expr=expr,
                    )
                )
        elif isinstance(stmt, NFunctionDef):
            result.append(stmt)
        else:
            result.append(stmt)
    return result


def _is_inlineable(
    sid: SymbolId,
    classifications: dict[SymbolId, InlineClassification],
    local_funcs: dict[SymbolId, NFunctionDef],
) -> bool:
    cls = classifications.get(sid)
    return cls is not None and cls.is_pure and sid in local_funcs
