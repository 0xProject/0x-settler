"""
Pure helper inlining on the normalized imperative IR.

Replaces ``NLocalCall`` nodes to pure helpers (no memory, no leave,
no for-loops) with the helper's body evaluated as a symbolic
expression.  This is the normalized-IR equivalent of the old
pipeline's ``_inline_single_call()`` + ``inline_calls()``.

Architecture:
- ``inline_pure_helpers()`` is a recursive block-to-block IR transform
- Switch statements are pre-normalized to nested NIf before inlining
- Multi-target assignments use fresh temporaries to preserve
  simultaneous-assignment semantics
- Symbolic execution of helper bodies handles multi-return internally
"""

from __future__ import annotations

from typing import assert_never

from norm_classify import (
    InlineClassification,
    _is_uint512_from_shape,
    classify_function_scope,
)
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
    sid_map: dict[SymbolId, SymbolId] = {}
    for old_sid in collisions:
        new_sid = alloc.alloc()
        rename_map[old_sid] = NRef(symbol_id=new_sid, name=f"_inl_{old_sid._id}")
        sid_map[old_sid] = new_sid

    new_body = _substitute_block(fdef.body, rename_map)
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
        return stmt
    if isinstance(stmt, NExprEffect):
        return NExprEffect(expr=substitute_nexpr(stmt.expr, subst))
    if isinstance(stmt, (NFor, NLeave, NSwitch)):
        return stmt
    assert_never(stmt)


def _remap_bind_targets(block: NBlock, sid_map: dict[SymbolId, SymbolId]) -> NBlock:
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
# Switch → nested-NIf pre-normalization
# ---------------------------------------------------------------------------


def _normalize_switch_to_if(stmt: NSwitch) -> NStmt:
    """Convert ``NSwitch`` to nested ``NIf`` + ``NIf(iszero(...))`` chain.

    The discriminant expression is duplicated into each condition.
    This is safe because the classifier rejects functions with
    effectful control-flow conditions (``has_effectful_condition``).

    Built bottom-up so the innermost block is the default (or empty).
    Exactly one branch executes, matching Yul switch semantics.
    """
    disc = stmt.discriminant
    tail: NBlock = stmt.default if stmt.default is not None else NBlock(())

    for case in reversed(stmt.cases):
        cond: NExpr = NBuiltinCall(op="eq", args=(disc, NConst(case.value.value)))
        inv_cond: NExpr = NBuiltinCall(op="iszero", args=(cond,))
        tail = NBlock(
            (
                NIf(condition=cond, then_body=case.body),
                NIf(condition=inv_cond, then_body=tail),
            )
        )

    return tail


def _pre_normalize_block(block: NBlock) -> NBlock:
    """Pre-normalize a block: convert NSwitch to NIf chains."""
    stmts: list[NStmt] = []
    for stmt in block.stmts:
        if isinstance(stmt, NSwitch):
            stmts.append(_normalize_switch_to_if(stmt))
        elif isinstance(stmt, NIf):
            stmts.append(
                NIf(
                    condition=stmt.condition,
                    then_body=_pre_normalize_block(stmt.then_body),
                )
            )
        elif isinstance(stmt, NBlock):
            stmts.append(_pre_normalize_block(stmt))
        elif isinstance(stmt, NFunctionDef):
            stmts.append(
                NFunctionDef(
                    name=stmt.name,
                    symbol_id=stmt.symbol_id,
                    params=stmt.params,
                    param_names=stmt.param_names,
                    returns=stmt.returns,
                    return_names=stmt.return_names,
                    body=_pre_normalize_block(stmt.body),
                )
            )
        else:
            stmts.append(stmt)
    return NBlock(tuple(stmts))


# ---------------------------------------------------------------------------
# Inline context (immutable defs map)
# ---------------------------------------------------------------------------


class _InlineCtx:
    """Immutable context for the inlining pass."""

    def __init__(
        self,
        defs: dict[SymbolId, NFunctionDef],
        classifications: dict[SymbolId, InlineClassification],
        alloc: SymbolAllocator,
        max_depth: int = 40,
    ) -> None:
        self.defs = defs
        self.classifications = classifications
        self.alloc = alloc
        self.max_depth = max_depth

    def is_inlineable(self, sid: SymbolId) -> bool:
        cls = self.classifications.get(sid)
        return cls is not None and cls.is_pure and sid in self.defs

    def is_uint512_from(self, sid: SymbolId) -> bool:
        cls = self.classifications.get(sid)
        if cls is None or not cls.is_deferred:
            return False
        fdef = self.defs.get(sid)
        return fdef is not None and _is_uint512_from_shape(fdef)


# ---------------------------------------------------------------------------
# Single-call inlining (pure helpers only)
# ---------------------------------------------------------------------------

_InlineResult = NExpr | tuple[NExpr, ...]


def inline_pure_call(
    fdef: NFunctionDef,
    args: tuple[NExpr, ...],
    ctx: _InlineCtx,
    *,
    depth: int = 0,
) -> _InlineResult:
    """Inline a single pure helper call, returning its return expression(s)."""
    if depth > ctx.max_depth:
        raise ParseError(
            f"Inlining depth limit ({ctx.max_depth}) exceeded for {fdef.name!r}"
        )

    fdef = _alpha_rename_if_needed(fdef, args, ctx.alloc)

    # Seed substitution: params → args, returns → 0.
    subst: dict[SymbolId, NExpr] = {}
    for sid, arg in zip(fdef.params, args):
        subst[sid] = arg
    for sid in fdef.returns:
        subst[sid] = NConst(0)

    # leave_info: if a leave was encountered in an if-block, stores
    # (condition, if-branch substitution). Only one leave site allowed.
    leave_info: tuple[NExpr, dict[SymbolId, NExpr]] | None = None
    block_result = _process_pure_block(fdef.body, subst, ctx, depth, leave_info)
    if block_result is not True and isinstance(block_result, tuple):
        leave_info = block_result

    # Merge leave path with else path.
    if leave_info is not None:
        l_cond, l_subst = leave_info
        for sid in fdef.returns:
            if_val = l_subst.get(sid, NConst(0))
            else_val = subst.get(sid, NConst(0))
            subst[sid] = _simplify_ite(l_cond, if_val, else_val)

    if len(fdef.returns) == 1:
        return subst[fdef.returns[0]]
    return tuple(subst[sid] for sid in fdef.returns)


_LeaveInfo = tuple[NExpr, dict[SymbolId, NExpr]] | None


def _process_pure_block(
    block: NBlock,
    subst: dict[SymbolId, NExpr],
    ctx: _InlineCtx,
    depth: int,
    leave_info: _LeaveInfo,
) -> _LeaveInfo | bool:
    """Process a block. Returns:
    - True: direct/unconditional leave encountered, stop processing
    - tuple: conditional leave_info (leave inside non-constant if)
    - None: no leave
    """
    for stmt in block.stmts:
        result = _process_pure_stmt(stmt, subst, ctx, depth, leave_info)
        if result is True:
            return True
        if isinstance(result, tuple):
            leave_info = result
    return leave_info


def _process_pure_stmt(
    stmt: NStmt,
    subst: dict[SymbolId, NExpr],
    ctx: _InlineCtx,
    depth: int,
    leave_info: _LeaveInfo,
) -> _LeaveInfo | bool:
    """Process one statement. Returns:
    - None: normal, no leave
    - tuple: leave_info was set (leave in if-block)
    - True: direct leave encountered, stop processing
    """
    if isinstance(stmt, NBind):
        if stmt.expr is not None:
            _process_bind_or_assign(stmt.targets, stmt.expr, subst, ctx, depth)
        else:
            for sid in stmt.targets:
                subst[sid] = NConst(0)
        return leave_info

    if isinstance(stmt, NAssign):
        _process_bind_or_assign(stmt.targets, stmt.expr, subst, ctx, depth)
        return leave_info

    if isinstance(stmt, NIf):
        cond = substitute_nexpr(stmt.condition, subst)
        cond = _inline_in_expr(cond, ctx, depth)

        c = _try_const(cond)
        if c is not None:
            if c != 0:
                # Constant-true branch. Propagate leave signal if body leaves.
                inner = _process_pure_block(
                    stmt.then_body, subst, ctx, depth, leave_info
                )
                if inner is True:
                    return True
                if isinstance(inner, tuple):
                    return inner
                return leave_info
            # Constant-false: dead branch.
            return leave_info

        # Non-constant condition.
        if_subst = dict(subst)
        inner_leave = _process_pure_block(stmt.then_body, if_subst, ctx, depth, None)

        if inner_leave is not None or _block_has_leave(stmt.then_body):
            # Leave in the if-body: save as leave_info.
            if leave_info is not None:
                raise ParseError("Multiple leave sites in pure helper")
            # Use if_subst as the leave-branch state.
            # Don't merge into subst — remaining stmts use pre-if state.
            return (cond, if_subst)

        # Normal if (no leave): merge branches.
        for sid in if_subst:
            if if_subst[sid] is not subst.get(sid):
                pre_val = subst.get(sid, NConst(0))
                subst[sid] = _simplify_ite(cond, if_subst[sid], pre_val)
        return leave_info

    if isinstance(stmt, NFunctionDef):
        return leave_info

    if isinstance(stmt, NBlock):
        return _process_pure_block(stmt, subst, ctx, depth, leave_info)

    if isinstance(stmt, NLeave):
        return True

    if isinstance(stmt, (NFor, NExprEffect, NSwitch)):
        raise ParseError(f"Unexpected {type(stmt).__name__} in pure helper body")

    assert_never(stmt)


def _block_has_leave(block: NBlock) -> bool:
    """Check if a block directly contains NLeave (non-recursive into sub-blocks)."""
    for stmt in block.stmts:
        if isinstance(stmt, NLeave):
            return True
    return False


def _process_bind_or_assign(
    targets: tuple[SymbolId, ...],
    expr: NExpr,
    subst: dict[SymbolId, NExpr],
    ctx: _InlineCtx,
    depth: int,
) -> None:
    """Process a bind/assign, handling multi-target with simultaneous semantics."""
    resolved = substitute_nexpr(expr, subst)

    if len(targets) == 1:
        # Single target: inline in expression, assign.
        resolved = _inline_in_expr(resolved, ctx, depth)
        subst[targets[0]] = resolved
        return

    # Multi-target: the RHS must be a multi-return call.
    # Inline the call to get a tuple of expressions, then assign
    # ALL targets simultaneously (evaluate all values before assigning).
    multi_result = _inline_in_expr_multi(resolved, ctx, depth)
    if isinstance(multi_result, tuple):
        vals: tuple[NExpr, ...] = multi_result
        if len(vals) != len(targets):
            raise ParseError(
                f"Multi-return arity mismatch: {len(targets)} targets, "
                f"{len(vals)} values"
            )
        for sid, val in zip(targets, vals):
            subst[sid] = val
    else:
        raise ParseError(
            f"Multi-target assignment requires multi-return call, " f"got single value"
        )


def _inline_in_expr_multi(
    expr: NExpr,
    ctx: _InlineCtx,
    depth: int,
) -> _InlineResult:
    """Inline a call that may return multiple values (for multi-target assignment)."""
    if isinstance(expr, NLocalCall):
        new_args = tuple(_inline_in_expr(a, ctx, depth) for a in expr.args)
        if ctx.is_inlineable(expr.symbol_id):
            fdef = ctx.defs[expr.symbol_id]
            return inline_pure_call(fdef, new_args, ctx, depth=depth + 1)
        return NLocalCall(symbol_id=expr.symbol_id, name=expr.name, args=new_args)
    # Non-call or non-inlineable: just inline as scalar.
    return _inline_in_expr(expr, ctx, depth)


# ---------------------------------------------------------------------------
# Inline calls within expressions (scalar only)
# ---------------------------------------------------------------------------


def _inline_in_expr(
    expr: NExpr,
    ctx: _InlineCtx,
    depth: int,
) -> NExpr:
    """Recursively inline pure helper calls within an expression (scalar context)."""
    if isinstance(expr, (NConst, NRef)):
        return expr

    if isinstance(expr, NBuiltinCall):
        new_args = tuple(_inline_in_expr(a, ctx, depth) for a in expr.args)
        return NBuiltinCall(op=expr.op, args=new_args)

    if isinstance(expr, NLocalCall):
        new_args = tuple(_inline_in_expr(a, ctx, depth) for a in expr.args)
        if ctx.is_inlineable(expr.symbol_id):
            fdef = ctx.defs[expr.symbol_id]
            result = inline_pure_call(fdef, new_args, ctx, depth=depth + 1)
            if isinstance(result, tuple):
                raise ParseError(
                    f"Multi-return call to {expr.name!r} in single-value context"
                )
            return result
        return NLocalCall(symbol_id=expr.symbol_id, name=expr.name, args=new_args)

    if isinstance(expr, NTopLevelCall):
        new_args = tuple(_inline_in_expr(a, ctx, depth) for a in expr.args)
        return NTopLevelCall(name=expr.name, args=new_args)

    if isinstance(expr, NUnresolvedCall):
        new_args = tuple(_inline_in_expr(a, ctx, depth) for a in expr.args)
        return NUnresolvedCall(name=expr.name, args=new_args)

    if isinstance(expr, NIte):
        return NIte(
            cond=_inline_in_expr(expr.cond, ctx, depth),
            if_true=_inline_in_expr(expr.if_true, ctx, depth),
            if_false=_inline_in_expr(expr.if_false, ctx, depth),
        )

    assert_never(expr)


# ---------------------------------------------------------------------------
# Block-level rewrite (recursive IR-to-IR transform)
# ---------------------------------------------------------------------------


def _rewrite_block(block: NBlock, ctx: _InlineCtx) -> NBlock:
    """Recursively rewrite a block, inlining pure calls at all depths."""
    stmts: list[NStmt] = []
    for stmt in block.stmts:
        stmts.extend(_rewrite_stmt(stmt, ctx))
    return NBlock(tuple(stmts))


def _rewrite_stmt(stmt: NStmt, ctx: _InlineCtx) -> list[NStmt]:
    """Rewrite a single statement, possibly expanding into multiple."""
    if isinstance(stmt, NBind):
        return _rewrite_bind_or_assign(
            stmt.targets, stmt.target_names, stmt.expr, ctx, is_bind=True
        )

    if isinstance(stmt, NAssign):
        return _rewrite_bind_or_assign(
            stmt.targets, stmt.target_names, stmt.expr, ctx, is_bind=False
        )

    if isinstance(stmt, NExprEffect):
        # Pure zero-return helper calls: the call itself can be dropped
        # (pure = no effects), but arguments may be effectful and must
        # be preserved as expression-statements.
        if isinstance(stmt.expr, NLocalCall) and ctx.is_inlineable(stmt.expr.symbol_id):
            fdef = ctx.defs[stmt.expr.symbol_id]
            if len(fdef.returns) == 0:
                result: list[NStmt] = []
                for arg in stmt.expr.args:
                    inlined_arg = _inline_in_expr(arg, ctx, 0)
                    if not isinstance(inlined_arg, NConst) and not isinstance(
                        inlined_arg, NRef
                    ):
                        result.append(NExprEffect(expr=inlined_arg))
                return result
        return [NExprEffect(expr=_inline_in_expr(stmt.expr, ctx, 0))]

    if isinstance(stmt, NIf):
        new_cond = _inline_in_expr(stmt.condition, ctx, 0)
        new_body = _rewrite_block(stmt.then_body, ctx)
        return [NIf(condition=new_cond, then_body=new_body)]

    if isinstance(stmt, NSwitch):
        # Should have been pre-normalized to NIf, but handle gracefully.
        new_disc = _inline_in_expr(stmt.discriminant, ctx, 0)
        new_cases = tuple(
            type(c)(value=c.value, body=_rewrite_block(c.body, ctx)) for c in stmt.cases
        )
        new_default = (
            _rewrite_block(stmt.default, ctx) if stmt.default is not None else None
        )
        return [NSwitch(discriminant=new_disc, cases=new_cases, default=new_default)]

    if isinstance(stmt, NFor):
        return [
            NFor(
                init=_rewrite_block(stmt.init, ctx),
                condition=_inline_in_expr(stmt.condition, ctx, 0),
                post=_rewrite_block(stmt.post, ctx),
                body=_rewrite_block(stmt.body, ctx),
            )
        ]

    if isinstance(stmt, NLeave):
        return [stmt]

    if isinstance(stmt, NBlock):
        return [_rewrite_block(stmt, ctx)]

    if isinstance(stmt, NFunctionDef):
        return [stmt]

    assert_never(stmt)


def _rewrite_bind_or_assign(
    targets: tuple[SymbolId, ...],
    target_names: tuple[str, ...],
    expr: NExpr | None,
    ctx: _InlineCtx,
    *,
    is_bind: bool,
) -> list[NStmt]:
    """Rewrite a bind/assign statement, handling multi-return with fresh temps."""
    if expr is None:
        return [NBind(targets=targets, target_names=target_names, expr=None)]

    cls = NBind if is_bind else NAssign

    if len(targets) == 1:
        # Check for uint512.from deferred inlining.
        if isinstance(expr, NLocalCall) and ctx.is_uint512_from(expr.symbol_id):
            return _inline_uint512_from(
                targets[0], target_names[0], expr, ctx, is_bind=is_bind
            )
        new_expr = _inline_in_expr(expr, ctx, 0)
        return [cls(targets=targets, target_names=target_names, expr=new_expr)]

    # Multi-target: check if the RHS is an inlineable call.
    if isinstance(expr, NLocalCall) and ctx.is_inlineable(expr.symbol_id):
        fdef = ctx.defs[expr.symbol_id]
        new_args = tuple(_inline_in_expr(a, ctx, 0) for a in expr.args)
        result = inline_pure_call(fdef, new_args, ctx, depth=1)
        if isinstance(result, tuple) and len(result) == len(targets):
            # Simultaneous assignment: bind each value to a fresh temp,
            # then assign targets from temps.
            temp_ids: list[SymbolId] = []
            temp_binds: list[NStmt] = []
            for i, val in enumerate(result):
                tid = ctx.alloc.alloc()
                temp_ids.append(tid)
                temp_binds.append(
                    NBind(
                        targets=(tid,),
                        target_names=(f"_tmp_{tid._id}",),
                        expr=val,
                    )
                )
            assigns: list[NStmt] = []
            for sid, name, tid in zip(targets, target_names, temp_ids):
                assigns.append(
                    cls(
                        targets=(sid,),
                        target_names=(name,),
                        expr=NRef(symbol_id=tid, name=f"_tmp_{tid._id}"),
                    )
                )
            return temp_binds + assigns

    # Not inlineable or not a call: inline within expression, pass through.
    new_expr = _inline_in_expr(expr, ctx, 0)
    return [cls(targets=targets, target_names=target_names, expr=new_expr)]


def _inline_uint512_from(
    target: SymbolId,
    target_name: str,
    call: NLocalCall,
    ctx: _InlineCtx,
    *,
    is_bind: bool,
) -> list[NStmt]:
    """Inline a uint512.from helper by emitting explicit mstore statements.

    Replaces ``ptr := from_helper(ptr_val, hi_val, lo_val)`` with:
        mstore(ptr_val, hi_val)
        mstore(add(0x20, ptr_val), lo_val)
        ptr := ptr_val

    This makes memory effects explicit in the IR (no sink side-channel).
    """
    if len(call.args) != 3:
        raise ParseError(
            f"uint512.from helper {call.name!r} expected 3 args, got {len(call.args)}"
        )
    ptr_arg = _inline_in_expr(call.args[0], ctx, 0)
    hi_arg = _inline_in_expr(call.args[1], ctx, 0)
    lo_arg = _inline_in_expr(call.args[2], ctx, 0)

    # Emit: mstore(ptr, hi)
    mstore_hi = NExprEffect(expr=NBuiltinCall(op="mstore", args=(ptr_arg, hi_arg)))
    # Emit: mstore(add(0x20, ptr), lo)
    lo_addr: NExpr = NBuiltinCall(op="add", args=(NConst(0x20), ptr_arg))
    mstore_lo = NExprEffect(expr=NBuiltinCall(op="mstore", args=(lo_addr, lo_arg)))
    # Emit: target := ptr
    cls = NBind if is_bind else NAssign
    assign_ptr = cls(targets=(target,), target_names=(target_name,), expr=ptr_arg)

    return [mstore_hi, mstore_lo, assign_ptr]


# ---------------------------------------------------------------------------
# Collect all function defs
# ---------------------------------------------------------------------------


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


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def inline_pure_helpers(
    func: NormalizedFunction,
) -> NormalizedFunction:
    """Inline all pure helper calls in *func*.

    1. Classify helpers on the unmodified body
    2. Pre-normalize switch → nested-if ONLY in pure helper bodies
       (the outer function and non-pure helpers are not touched)
    3. Recursively rewrite the body, inlining pure calls at all depths
    """
    classifications = classify_function_scope(func)
    alloc = SymbolAllocator(_max_symbol_id_impl(func) + 1)

    defs: dict[SymbolId, NFunctionDef] = {}
    _collect_all_fdefs(func.body, defs)

    # Pre-normalize switch → if ONLY in pure helper bodies.
    # The outer function body and non-pure helpers are left untouched.
    for sid in defs:
        cls = classifications.get(sid)
        if cls is not None and cls.is_pure:
            old = defs[sid]
            defs[sid] = NFunctionDef(
                name=old.name,
                symbol_id=old.symbol_id,
                params=old.params,
                param_names=old.param_names,
                returns=old.returns,
                return_names=old.return_names,
                body=_pre_normalize_block(old.body),
            )

    ctx = _InlineCtx(defs=defs, classifications=classifications, alloc=alloc)
    new_body = _rewrite_block(func.body, ctx)

    return NormalizedFunction(
        name=func.name,
        params=func.params,
        param_names=func.param_names,
        returns=func.returns,
        return_names=func.return_names,
        body=new_body,
    )
