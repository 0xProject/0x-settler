"""
Block-based helper inlining on the normalized imperative IR.

Architecture (per critic recommendation):
- Inlining a call returns an ``InlineFragment`` (prelude + results),
  not just an expression.  This cleanly separates effect emission
  from result computation.
- Arguments are atomized (bound to fresh temps) before inlining,
  ensuring single evaluation.
- Leave is represented as control flow (``did_leave`` flag) rather
  than expression-level ``(cond, subst)`` merging.
- Strategy classification drives which path each helper takes:
  ``ExprInline``, ``BlockInline``, ``EffectLower``, ``DoNotInline``.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from norm_classify import (
    InlineClassification,
    InlineStrategy,
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
    NStore,
    NSwitch,
    NSwitchCase,
    NTopLevelCall,
    NUnresolvedCall,
)
from norm_walk import (
    collect_function_defs,
    for_each_expr,
    map_expr,
    max_symbol_id,
)
from yul_ast import ParseError, SymbolId

# ---------------------------------------------------------------------------
# SymbolId allocator
# ---------------------------------------------------------------------------


class SymbolAllocator:
    """Generates fresh ``SymbolId`` values."""

    def __init__(self, start: int) -> None:
        self._next = start

    def alloc(self) -> SymbolId:
        sid = SymbolId(self._next)
        self._next += 1
        return sid


# ---------------------------------------------------------------------------
# InlineFragment — the universal inlining result
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class InlineFragment:
    """Result of inlining a helper call.

    ``prelude`` contains statements that must be emitted before the
    result values are used (argument bindings, effect statements,
    did_leave guards).

    ``results`` contains one expression per return value.
    """

    prelude: tuple[NStmt, ...]
    results: tuple[NExpr, ...]


# ---------------------------------------------------------------------------
# Argument atomization
# ---------------------------------------------------------------------------


def _atomize_args(
    args: tuple[NExpr, ...],
    alloc: SymbolAllocator,
) -> tuple[tuple[NStmt, ...], tuple[NRef, ...]]:
    """Bind each argument to a fresh temp, returning (binds, refs).

    Ensures each argument is evaluated exactly once, in order.
    Trivial atoms (NConst, NRef) are passed through without a temp.
    """
    binds: list[NStmt] = []
    refs: list[NRef] = []
    for arg in args:
        if isinstance(arg, (NConst, NRef)):
            # Already atomic — no temp needed, but we need an NRef.
            # For NConst, we still bind to avoid duplicating large constants.
            if isinstance(arg, NRef):
                refs.append(arg)
                continue
        tid = alloc.alloc()
        name = f"_arg_{tid._id}"
        binds.append(NBind(targets=(tid,), target_names=(name,), expr=arg))
        refs.append(NRef(symbol_id=tid, name=name))
    return tuple(binds), tuple(refs)


# ---------------------------------------------------------------------------
# Expression substitution (via shared map_expr)
# ---------------------------------------------------------------------------


def substitute_nexpr(
    expr: NExpr,
    subst: dict[SymbolId, NExpr],
) -> NExpr:
    """Replace ``NRef`` nodes according to *subst*."""

    def rewrite(e: NExpr) -> NExpr:
        if isinstance(e, NRef):
            return subst.get(e.symbol_id, e)
        return e

    return map_expr(expr, rewrite)


# ---------------------------------------------------------------------------
# Simplify Ite
# ---------------------------------------------------------------------------


def _try_const(expr: NExpr) -> int | None:
    if isinstance(expr, NConst):
        return expr.value
    return None


def _simplify_ite(cond: NExpr, if_true: NExpr, if_false: NExpr) -> NExpr:
    if if_true == if_false:
        return if_true
    c = _try_const(cond)
    if c is not None:
        return if_true if c != 0 else if_false
    return NIte(cond=cond, if_true=if_true, if_false=if_false)


# ---------------------------------------------------------------------------
# Switch → nested-NIf pre-normalization
# ---------------------------------------------------------------------------


def _normalize_switch_to_if(stmt: NSwitch) -> NStmt:
    """Convert ``NSwitch`` to nested ``NIf`` chain.

    Safe because the classifier rejects effectful conditions.
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
# Inline context
# ---------------------------------------------------------------------------


class _InlineCtx:
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

    def strategy_for(self, sid: SymbolId) -> InlineStrategy:
        cls = self.classifications.get(sid)
        if cls is None:
            return InlineStrategy.DO_NOT_INLINE
        return cls.strategy


# ---------------------------------------------------------------------------
# ExprInline: symbolic execution of pure helper body
# ---------------------------------------------------------------------------


def _expr_inline(
    fdef: NFunctionDef,
    atom_args: tuple[NExpr, ...],
    ctx: _InlineCtx,
    depth: int,
) -> InlineFragment:
    """Inline a pure helper via symbolic expression substitution."""
    subst: dict[SymbolId, NExpr] = {}
    for sid, arg in zip(fdef.params, atom_args):
        subst[sid] = arg
    for sid in fdef.returns:
        subst[sid] = NConst(0)

    _symex_block(fdef.body, subst, ctx, depth)

    results = tuple(subst[sid] for sid in fdef.returns)
    return InlineFragment(prelude=(), results=results)


def _symex_block(
    block: NBlock,
    subst: dict[SymbolId, NExpr],
    ctx: _InlineCtx,
    depth: int,
) -> None:
    for stmt in block.stmts:
        _symex_stmt(stmt, subst, ctx, depth)


def _symex_stmt(
    stmt: NStmt,
    subst: dict[SymbolId, NExpr],
    ctx: _InlineCtx,
    depth: int,
) -> None:
    if isinstance(stmt, (NBind, NAssign)):
        if isinstance(stmt, NBind) and stmt.expr is None:
            for sid in stmt.targets:
                subst[sid] = NConst(0)
            return
        expr = stmt.expr
        assert expr is not None
        resolved = substitute_nexpr(expr, subst)
        if len(stmt.targets) == 1:
            resolved = _inline_in_expr(resolved, ctx, depth)
            subst[stmt.targets[0]] = resolved
        else:
            # Multi-target: try multi-return inline BEFORE scalar inline.
            multi = _try_inline_multi(resolved, ctx, depth)
            if isinstance(multi, tuple) and len(multi) == len(stmt.targets):
                for sid, val in zip(stmt.targets, multi):
                    subst[sid] = val
            else:
                resolved = _inline_in_expr(resolved, ctx, depth)
                subst[stmt.targets[0]] = resolved
        return

    if isinstance(stmt, NIf):
        cond = substitute_nexpr(stmt.condition, subst)
        cond = _inline_in_expr(cond, ctx, depth)
        c = _try_const(cond)
        if c is not None:
            if c != 0:
                _symex_block(stmt.then_body, subst, ctx, depth)
            return
        if_subst = dict(subst)
        _symex_block(stmt.then_body, if_subst, ctx, depth)
        for sid in if_subst:
            if if_subst[sid] is not subst.get(sid):
                pre_val = subst.get(sid, NConst(0))
                subst[sid] = _simplify_ite(cond, if_subst[sid], pre_val)
        return

    if isinstance(stmt, (NFunctionDef, NBlock)):
        if isinstance(stmt, NBlock):
            _symex_block(stmt, subst, ctx, depth)
        return

    if isinstance(stmt, (NFor, NLeave, NExprEffect, NSwitch, NStore)):
        raise ParseError(f"Unexpected {type(stmt).__name__} in ExprInline body")


def _try_inline_multi(
    expr: NExpr, ctx: _InlineCtx, depth: int
) -> tuple[NExpr, ...] | NExpr:
    """Try to inline a multi-return call, returning tuple or single expr."""
    if isinstance(expr, NLocalCall):
        strat = ctx.strategy_for(expr.symbol_id)
        if strat == InlineStrategy.EXPR_INLINE and expr.symbol_id in ctx.defs:
            fdef = ctx.defs[expr.symbol_id]
            frag = _expr_inline(fdef, expr.args, ctx, depth + 1)
            if len(frag.results) > 1:
                return frag.results
            if len(frag.results) == 1:
                return frag.results[0]
    return expr


# ---------------------------------------------------------------------------
# BlockInline: clone body with did_leave flag
# ---------------------------------------------------------------------------


def _block_inline(
    fdef: NFunctionDef,
    atom_args: tuple[NExpr, ...],
    alloc: SymbolAllocator,
) -> InlineFragment:
    """Inline a leave-bearing helper by cloning its body.

    Uses a ``did_leave`` flag: leave becomes ``did_leave := 1``,
    and subsequent statements are guarded with ``if iszero(did_leave)``.
    """
    prelude: list[NStmt] = []

    # Fresh return temps.
    ret_temps: list[SymbolId] = []
    for i, sid in enumerate(fdef.returns):
        tid = alloc.alloc()
        ret_temps.append(tid)
        prelude.append(
            NBind(
                targets=(tid,),
                target_names=(f"_ret_{tid._id}",),
                expr=NConst(0),
            )
        )

    # did_leave flag.
    did_leave_id = alloc.alloc()
    did_leave_ref = NRef(symbol_id=did_leave_id, name=f"_did_leave_{did_leave_id._id}")
    prelude.append(
        NBind(
            targets=(did_leave_id,),
            target_names=(f"_did_leave_{did_leave_id._id}",),
            expr=NConst(0),
        )
    )

    # Build substitution: params → atom_args, returns → ret_temps.
    subst: dict[SymbolId, SymbolId] = {}
    for old_sid, arg_ref in zip(fdef.params, atom_args):
        if isinstance(arg_ref, NRef):
            subst[old_sid] = arg_ref.symbol_id
    for old_sid, new_sid in zip(fdef.returns, ret_temps):
        subst[old_sid] = new_sid

    # Clone body with substitutions.
    cloned = _clone_body_for_block_inline(
        fdef.body, subst, did_leave_id, did_leave_ref, alloc
    )
    prelude.extend(cloned)

    results = tuple(NRef(symbol_id=tid, name=f"_ret_{tid._id}") for tid in ret_temps)
    return InlineFragment(prelude=tuple(prelude), results=results)


def _clone_body_for_block_inline(
    block: NBlock,
    sid_map: dict[SymbolId, SymbolId],
    did_leave_id: SymbolId,
    did_leave_ref: NExpr,
    alloc: SymbolAllocator,
) -> list[NStmt]:
    """Clone a helper body, rewriting leave as ``did_leave := 1``.

    Every statement after the first that could set ``did_leave``
    (direct NLeave, or NIf whose body may leave) is wrapped in
    ``if iszero(did_leave) { ... }`` to skip it after early exit.
    """
    out: list[NStmt] = []
    may_have_left = False

    for stmt in block.stmts:
        if isinstance(stmt, NLeave):
            out.append(
                NAssign(
                    targets=(did_leave_id,),
                    target_names=(f"_did_leave_{did_leave_id._id}",),
                    expr=NConst(1),
                )
            )
            may_have_left = True
            continue

        remapped = _remap_stmt(stmt, sid_map, did_leave_id, did_leave_ref, alloc)

        if may_have_left:
            # Guard this statement with if iszero(did_leave).
            guard_cond = NBuiltinCall(op="iszero", args=(did_leave_ref,))
            out.append(NIf(condition=guard_cond, then_body=NBlock((remapped,))))
        else:
            out.append(remapped)

        # If this statement might contain a leave (e.g. NIf with leave body),
        # subsequent statements need guarding.
        if _stmt_may_leave(stmt):
            may_have_left = True

    return out


def _stmt_may_leave(stmt: NStmt) -> bool:
    """Check if a statement might set the did_leave flag."""
    if isinstance(stmt, NLeave):
        return True
    if isinstance(stmt, NIf):
        return any(_stmt_may_leave(s) for s in stmt.then_body.stmts)
    if isinstance(stmt, NBlock):
        return any(_stmt_may_leave(s) for s in stmt.stmts)
    return False


def _remap_expr(expr: NExpr, sid_map: dict[SymbolId, SymbolId]) -> NExpr:
    """Remap SymbolIds in an expression."""

    def rewrite(e: NExpr) -> NExpr:
        if isinstance(e, NRef) and e.symbol_id in sid_map:
            return NRef(symbol_id=sid_map[e.symbol_id], name=e.name)
        if isinstance(e, NLocalCall) and e.symbol_id in sid_map:
            return NLocalCall(symbol_id=sid_map[e.symbol_id], name=e.name, args=e.args)
        return e

    return map_expr(expr, rewrite)


def _remap_stmt(
    stmt: NStmt,
    sid_map: dict[SymbolId, SymbolId],
    did_leave_id: SymbolId,
    did_leave_ref: NExpr,
    alloc: SymbolAllocator,
) -> NStmt:
    """Remap a single statement for block-inline."""
    if isinstance(stmt, NBind):
        new_targets = tuple(sid_map.get(s, s) for s in stmt.targets)
        new_expr = _remap_expr(stmt.expr, sid_map) if stmt.expr is not None else None
        return NBind(targets=new_targets, target_names=stmt.target_names, expr=new_expr)
    if isinstance(stmt, NAssign):
        new_targets = tuple(sid_map.get(s, s) for s in stmt.targets)
        return NAssign(
            targets=new_targets,
            target_names=stmt.target_names,
            expr=_remap_expr(stmt.expr, sid_map),
        )
    if isinstance(stmt, NIf):
        inner = _clone_body_for_block_inline(
            stmt.then_body, sid_map, did_leave_id, did_leave_ref, alloc
        )
        return NIf(
            condition=_remap_expr(stmt.condition, sid_map),
            then_body=NBlock(tuple(inner)),
        )
    if isinstance(stmt, NBlock):
        inner = _clone_body_for_block_inline(
            stmt, sid_map, did_leave_id, did_leave_ref, alloc
        )
        return NBlock(tuple(inner))
    if isinstance(stmt, NExprEffect):
        return NExprEffect(expr=_remap_expr(stmt.expr, sid_map))
    if isinstance(stmt, NStore):
        return NStore(
            addr=_remap_expr(stmt.addr, sid_map),
            value=_remap_expr(stmt.value, sid_map),
        )
    if isinstance(stmt, NFunctionDef):
        return stmt
    if isinstance(stmt, NLeave):
        # Should be handled by _clone_body_for_block_inline.
        raise ParseError("Unexpected NLeave in _remap_stmt")
    if isinstance(stmt, (NFor, NSwitch)):
        return stmt
    raise ParseError(f"Unexpected {type(stmt).__name__} in block-inline")


# ---------------------------------------------------------------------------
# EffectLower: uint512.from → explicit NStore
# ---------------------------------------------------------------------------


def _effect_lower(
    fdef: NFunctionDef,
    atom_args: tuple[NExpr, ...],
    alloc: SymbolAllocator,
) -> InlineFragment:
    """Lower a uint512.from helper into explicit NStore statements."""
    if len(atom_args) != 3 or len(fdef.returns) != 1:
        raise ParseError(f"EffectLower for {fdef.name!r}: expected 3 args / 1 return")
    ptr, hi, lo = atom_args
    lo_addr: NExpr = NBuiltinCall(op="add", args=(NConst(0x20), ptr))
    prelude: tuple[NStmt, ...] = (
        NStore(addr=ptr, value=hi),
        NStore(addr=lo_addr, value=lo),
    )
    return InlineFragment(prelude=prelude, results=(ptr,))


# ---------------------------------------------------------------------------
# Expression-level inlining (scalar context)
# ---------------------------------------------------------------------------


def _inline_in_expr(expr: NExpr, ctx: _InlineCtx, depth: int) -> NExpr:
    """Inline pure helper calls within an expression (scalar context only)."""
    if isinstance(expr, (NConst, NRef)):
        return expr

    if isinstance(expr, NBuiltinCall):
        new_args = tuple(_inline_in_expr(a, ctx, depth) for a in expr.args)
        return NBuiltinCall(op=expr.op, args=new_args)

    if isinstance(expr, NLocalCall):
        new_args = tuple(_inline_in_expr(a, ctx, depth) for a in expr.args)
        strat = ctx.strategy_for(expr.symbol_id)
        if strat == InlineStrategy.EXPR_INLINE and expr.symbol_id in ctx.defs:
            if depth > ctx.max_depth:
                raise ParseError(f"Inlining depth exceeded for {expr.name!r}")
            fdef = ctx.defs[expr.symbol_id]
            frag = _expr_inline(fdef, new_args, ctx, depth + 1)
            if len(frag.results) == 1:
                return frag.results[0]
            raise ParseError(
                f"Multi-return call to {expr.name!r} in single-value context"
            )
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

    raise ParseError(f"Unexpected expression type: {type(expr).__name__}")


# ---------------------------------------------------------------------------
# Block-level rewrite (recursive IR-to-IR transform)
# ---------------------------------------------------------------------------


def _rewrite_block(block: NBlock, ctx: _InlineCtx) -> NBlock:
    stmts: list[NStmt] = []
    for stmt in block.stmts:
        stmts.extend(_rewrite_stmt(stmt, ctx))
    return NBlock(tuple(stmts))


def _rewrite_stmt(stmt: NStmt, ctx: _InlineCtx) -> list[NStmt]:
    if isinstance(stmt, (NBind, NAssign)):
        return _rewrite_bind_or_assign(stmt, ctx)

    if isinstance(stmt, NExprEffect):
        # Pure zero-return helper: preserve args, drop call.
        if isinstance(stmt.expr, NLocalCall):
            strat = ctx.strategy_for(stmt.expr.symbol_id)
            if strat == InlineStrategy.EXPR_INLINE:
                fdef = ctx.defs.get(stmt.expr.symbol_id)
                if fdef is not None and len(fdef.returns) == 0:
                    result: list[NStmt] = []
                    for arg in stmt.expr.args:
                        inlined = _inline_in_expr(arg, ctx, 0)
                        if not isinstance(inlined, (NConst, NRef)):
                            result.append(NExprEffect(expr=inlined))
                    return result
        return [NExprEffect(expr=_inline_in_expr(stmt.expr, ctx, 0))]

    if isinstance(stmt, NStore):
        return [
            NStore(
                addr=_inline_in_expr(stmt.addr, ctx, 0),
                value=_inline_in_expr(stmt.value, ctx, 0),
            )
        ]

    if isinstance(stmt, NIf):
        new_cond = _inline_in_expr(stmt.condition, ctx, 0)
        return [NIf(condition=new_cond, then_body=_rewrite_block(stmt.then_body, ctx))]

    if isinstance(stmt, NSwitch):
        new_disc = _inline_in_expr(stmt.discriminant, ctx, 0)
        new_cases = tuple(
            NSwitchCase(value=c.value, body=_rewrite_block(c.body, ctx))
            for c in stmt.cases
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

    if isinstance(stmt, (NLeave, NFunctionDef)):
        return [stmt]

    if isinstance(stmt, NBlock):
        return [_rewrite_block(stmt, ctx)]

    raise ParseError(f"Unexpected statement: {type(stmt).__name__}")


def _rewrite_bind_or_assign(
    stmt: NBind | NAssign,
    ctx: _InlineCtx,
) -> list[NStmt]:
    """Rewrite a bind/assign, using InlineFragment for all strategies."""
    expr = stmt.expr
    if isinstance(stmt, NBind) and expr is None:
        return [stmt]

    assert expr is not None
    is_bind = isinstance(stmt, NBind)
    cls_type = NBind if is_bind else NAssign

    # Check if the RHS is an inlineable call.
    if isinstance(expr, NLocalCall) and expr.symbol_id in ctx.defs:
        strat = ctx.strategy_for(expr.symbol_id)
        fdef = ctx.defs[expr.symbol_id]

        if strat != InlineStrategy.DO_NOT_INLINE:
            # Atomize arguments.
            raw_args = tuple(_inline_in_expr(a, ctx, 0) for a in expr.args)
            arg_binds, atom_refs = _atomize_args(raw_args, ctx.alloc)

            # Get InlineFragment from the appropriate strategy.
            frag: InlineFragment
            if strat == InlineStrategy.EXPR_INLINE:
                frag = _expr_inline(fdef, tuple(atom_refs), ctx, 1)
            elif strat == InlineStrategy.BLOCK_INLINE:
                frag = _block_inline(fdef, tuple(atom_refs), ctx.alloc)
            elif strat == InlineStrategy.EFFECT_LOWER:
                frag = _effect_lower(fdef, tuple(atom_refs), ctx.alloc)
            else:
                raise ParseError(f"Unknown strategy: {strat}")

            # Emit: arg binds → prelude → target assignments.
            out: list[NStmt] = list(arg_binds) + list(frag.prelude)

            if len(stmt.targets) == len(frag.results):
                if len(stmt.targets) == 1:
                    out.append(
                        cls_type(
                            targets=stmt.targets,
                            target_names=stmt.target_names,
                            expr=frag.results[0],
                        )
                    )
                else:
                    # Multi-return: use fresh temps for simultaneous assignment.
                    temp_ids: list[SymbolId] = []
                    for val in frag.results:
                        tid = ctx.alloc.alloc()
                        temp_ids.append(tid)
                        out.append(
                            NBind(
                                targets=(tid,),
                                target_names=(f"_tmp_{tid._id}",),
                                expr=val,
                            )
                        )
                    for sid, name, tid in zip(
                        stmt.targets, stmt.target_names, temp_ids
                    ):
                        out.append(
                            cls_type(
                                targets=(sid,),
                                target_names=(name,),
                                expr=NRef(symbol_id=tid, name=f"_tmp_{tid._id}"),
                            )
                        )
                return out

    # Not inlineable: just inline within expression.
    new_expr = _inline_in_expr(expr, ctx, 0)
    return [
        cls_type(targets=stmt.targets, target_names=stmt.target_names, expr=new_expr)
    ]


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def inline_pure_helpers(
    func: NormalizedFunction,
) -> NormalizedFunction:
    """Inline helpers according to their classification strategy.

    1. Classify all nested helpers
    2. Pre-normalize switch → if in pure/block-inline helper bodies
    3. Recursively rewrite the body
    """
    classifications = classify_function_scope(func)
    alloc = SymbolAllocator(max_symbol_id(func) + 1)

    defs: dict[SymbolId, NFunctionDef] = {
        fdef.symbol_id: fdef for fdef in collect_function_defs(func.body)
    }

    # Pre-normalize switch → if ONLY in inlineable helper bodies.
    for sid in defs:
        cls = classifications.get(sid)
        if cls is not None and cls.strategy in (
            InlineStrategy.EXPR_INLINE,
            InlineStrategy.BLOCK_INLINE,
        ):
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
