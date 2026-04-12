"""
Block-based helper inlining on the normalized imperative IR.

- Inlining a call returns an ``InlineFragment`` (prelude + results),
  not just an expression.  This cleanly separates effect emission
  from result computation.
- Arguments are atomized (bound to fresh temps) before inlining,
  ensuring single evaluation.
- Leave is represented as control flow (``did_leave`` flag) rather
  than expression-level ``(cond, subst)`` merging.
- Strategy classification drives which path each helper takes:
  ``ExprInline``, ``BlockInline``, ``DoNotInline``.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import assert_never

from .norm_classify import (
    FunctionSummary,
    InlineClassification,
    InlineStrategy,
    classify_helpers,
    summarize_function,
)
from .norm_ir import (
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
    NSwitchCase,
    NTopLevelCall,
    NUnresolvedCall,
)
from .norm_leave import lower_leave_block
from .norm_optimize_shared import simplify_ite
from .norm_walk import (
    SymbolAllocator,
    collect_function_defs,
    freshen_function_subtree,
    map_expr,
    map_function_def,
    map_stmt,
    max_symbol_id,
)
from .yul_ast import ParseError, SymbolId

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


@dataclass(frozen=True)
class InlineBoundaryPolicy:
    """Call-survival policy for one inlining run.

    By default, unsupported or deferred helpers may remain as calls.

    Selected-target translation uses a stricter policy: local helper calls and
    the chosen non-selected top-level helper closure are not allowed to survive
    past normalization, so they must be structurally inlined before
    simplification and validation.
    """

    inline_local_helpers: bool = False
    inline_top_level_helpers: frozenset[str] = frozenset()


# ---------------------------------------------------------------------------
# Argument atomization
# ---------------------------------------------------------------------------


def _atomize_args(
    args: tuple[NExpr, ...],
    alloc: SymbolAllocator,
) -> tuple[tuple[NStmt, ...], tuple[NRef, ...]]:
    """Bind each argument to a fresh temp, returning (binds, refs).

    Ensures each argument is evaluated exactly once, in order.
    NRef atoms are passed through without a temp; NConst values are
    bound to avoid duplicating large constants.
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


# ---------------------------------------------------------------------------
# Switch → nested-NIf pre-normalization
# ---------------------------------------------------------------------------


def _normalize_switch_to_if(stmt: NSwitch) -> NStmt:
    """Convert ``NSwitch`` to nested ``NIf`` chain.

    Safe because the classifier rejects effectful conditions.
    """
    disc = stmt.discriminant
    tail: NBlock = stmt.default if stmt.default is not None else NBlock(stmts=())
    for case in reversed(stmt.cases):
        cond: NExpr = NBuiltinCall(op="eq", args=(disc, NConst(case.value.value)))
        inv_cond: NExpr = NBuiltinCall(op="iszero", args=(cond,))
        tail = NBlock(
            stmts=(
                NIf(condition=cond, then_body=case.body),
                NIf(condition=inv_cond, then_body=tail),
            )
        )
    return tail


def _pre_normalize_block(block: NBlock) -> NBlock:
    defs = tuple(
        map_function_def(fdef, map_block_fn=_pre_normalize_block) for fdef in block.defs
    )
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
        else:
            stmts.append(stmt)
    return NBlock(defs=defs, stmts=tuple(stmts))


# ---------------------------------------------------------------------------
# Inline context
# ---------------------------------------------------------------------------


class _InlineCtx:
    def __init__(
        self,
        defs: dict[SymbolId, NFunctionDef],
        classifications: dict[SymbolId, InlineClassification],
        alloc: SymbolAllocator,
        top_level_name_to_sid: dict[str, SymbolId] | None = None,
        allowed_model_calls: frozenset[str] = frozenset(),
        boundary_policy: InlineBoundaryPolicy | None = None,
        max_depth: int = 40,
    ) -> None:
        self.defs = defs
        self.classifications = classifications
        self.alloc = alloc
        self.top_level_name_to_sid = (
            dict(top_level_name_to_sid) if top_level_name_to_sid is not None else {}
        )
        self.allowed_model_calls = allowed_model_calls
        self.boundary_policy = (
            boundary_policy if boundary_policy is not None else InlineBoundaryPolicy()
        )
        self.max_depth = max_depth

    def strategy_for(self, sid: SymbolId) -> InlineStrategy:
        cls = self.classifications.get(sid)
        if cls is None:
            return InlineStrategy.DO_NOT_INLINE
        return cls.strategy

    def classification_for(self, sid: SymbolId) -> InlineClassification | None:
        return self.classifications.get(sid)


def _effective_inline_strategy(
    cls: InlineClassification | None,
    *,
    must_inline: bool,
) -> InlineStrategy:
    """Pick the actual rewrite strategy for a helper call site.

    Classification remains strict: unsupported helpers are still classified as
    ``DO_NOT_INLINE``. Some call sites, however, are covered by an explicit
    boundary policy and are not allowed to survive as calls. For those sites,
    we structurally inline with ``BLOCK_INLINE`` and let later simplification +
    validation decide whether any live unsupported constructs remain.
    """

    if cls is None:
        return InlineStrategy.DO_NOT_INLINE

    strat = cls.strategy
    if strat == InlineStrategy.BLOCK_INLINE and cls.is_deferred and not must_inline:
        return InlineStrategy.DO_NOT_INLINE
    if strat != InlineStrategy.DO_NOT_INLINE:
        return strat
    return InlineStrategy.BLOCK_INLINE if must_inline else InlineStrategy.DO_NOT_INLINE


# ---------------------------------------------------------------------------
# Register nested defs from a freshened prelude into the inline context
# ---------------------------------------------------------------------------


def _register_nested_defs(block: NBlock, ctx: _InlineCtx) -> None:
    """Add freshened NFunctionDef nodes to ctx.defs + classifications.

    After freshen_function_subtree, the cloned prelude may contain
    NFunctionDefs with new SymbolIds. These must be registered so
    _rewrite_block can inline calls to them.
    """
    new_fdefs = collect_function_defs(block)
    if not new_fdefs:
        return

    summaries: dict[SymbolId, FunctionSummary] = {}
    for fdef in new_fdefs:
        ctx.defs[fdef.symbol_id] = fdef
        summaries[fdef.symbol_id] = summarize_function(
            fdef.body,
            top_level_inline_sids=ctx.top_level_name_to_sid,
            allowed_model_calls=ctx.allowed_model_calls,
        )

    new_cls = classify_helpers(summaries)
    ctx.classifications.update(new_cls)


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
                raise ParseError(
                    f"Multi-target assignment to non-inlineable call "
                    f"in ExprInline body (targets: {len(stmt.targets)})"
                )
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
                subst[sid] = simplify_ite(cond, if_subst[sid], pre_val)
        return

    if isinstance(stmt, NBlock):
        _symex_block(stmt, subst, ctx, depth)
        return

    if isinstance(stmt, (NFor, NLeave, NExprEffect, NSwitch)):
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

    Uses ``freshen_function_subtree`` for full binder hygiene, then
    lowers leave with the canonical subtree transform from
    ``norm_leave.py``.
    """
    # Phase 1: freshen the entire subtree (all binders, nested fdefs, refs).
    fresh = freshen_function_subtree(fdef, alloc)

    prelude: list[NStmt] = []

    # Fresh return temps (use the freshened return IDs).
    ret_ids = fresh.returns

    # Zero-initialize return temps.
    for rid in ret_ids:
        prelude.append(
            NBind(
                targets=(rid,),
                target_names=(f"_ret_{rid._id}",),
                expr=NConst(0),
            )
        )

    # did_leave flag.
    did_leave_id = alloc.alloc()
    prelude.append(
        NBind(
            targets=(did_leave_id,),
            target_names=(f"_did_leave_{did_leave_id._id}",),
            expr=NConst(0),
        )
    )

    # Build param substitution: fresh params → atom_args.
    param_subst: dict[SymbolId, NExpr] = {}
    for sid, arg in zip(fresh.params, atom_args):
        param_subst[sid] = arg

    # Clone body with param substitution + leave rewriting.
    cloned = _clone_body_for_block_inline(fresh.body, param_subst, did_leave_id)
    if cloned.defs or cloned.stmts:
        prelude.append(cloned)

    results = tuple(NRef(symbol_id=rid, name=f"_ret_{rid._id}") for rid in ret_ids)
    return InlineFragment(prelude=tuple(prelude), results=results)


def _clone_body_for_block_inline(
    block: NBlock,
    param_subst: dict[SymbolId, NExpr],
    did_leave_id: SymbolId,
) -> NBlock:
    """Clone a freshened helper body, substituting params and rewriting leave.

    The body must already be freshened via ``freshen_function_subtree``.
    ``param_subst`` maps freshened param SymbolIds → argument expressions.

    All ``NLeave`` nodes are lowered by the shared leave transformer,
    so nested blocks and loops reuse the same semantics as the
    top-level pipeline.
    """
    # Apply param substitution to the whole block first.
    subst_body = _subst_block(block, param_subst)

    return lower_leave_block(subst_body, did_leave_id)


def _subst_block(block: NBlock, subst: dict[SymbolId, NExpr]) -> NBlock:
    """Substitute expressions for SymbolIds in a block (param replacement)."""
    if not subst:
        return block
    return NBlock(
        defs=block.defs,
        stmts=tuple(
            map_stmt(
                s,
                map_expr_fn=lambda e: substitute_nexpr(e, subst),
                map_block_fn=lambda b: _subst_block(b, subst),
            )
            for s in block.stmts
        ),
    )


# ---------------------------------------------------------------------------
# Expression-level inlining (scalar context)
# ---------------------------------------------------------------------------


def _inline_in_expr(expr: NExpr, ctx: _InlineCtx, depth: int) -> NExpr:
    """Inline helper calls within an expression (scalar context, no prelude).

    Only handles EXPR_INLINE. For BLOCK_INLINE, use
    ``_inline_in_expr_with_prelude`` which can emit side-effect statements.
    """
    pre, result = _inline_in_expr_with_prelude(expr, ctx, depth)
    if pre:
        raise ParseError(
            "Non-EXPR_INLINE call in pure expression context "
            "(should use _inline_in_expr_with_prelude)"
        )
    return result


def _inline_in_expr_with_prelude(
    expr: NExpr, ctx: _InlineCtx, depth: int
) -> tuple[list[NStmt], NExpr]:
    """Inline helper calls, returning (prelude_stmts, result_expr).

    Handles all strategies: EXPR_INLINE produces empty prelude,
    BLOCK_INLINE produces prelude statements.
    """
    if isinstance(expr, (NConst, NRef)):
        return [], expr

    if isinstance(expr, NBuiltinCall):
        pre: list[NStmt] = []
        new_args: list[NExpr] = []
        for a in expr.args:
            a_pre, a_val = _inline_in_expr_with_prelude(a, ctx, depth)
            pre.extend(a_pre)
            new_args.append(a_val)
        return pre, NBuiltinCall(op=expr.op, args=tuple(new_args))

    if isinstance(expr, NLocalCall):
        # Inline arguments first.
        pre = []
        new_args_list: list[NExpr] = []
        for a in expr.args:
            a_pre, a_val = _inline_in_expr_with_prelude(a, ctx, depth)
            pre.extend(a_pre)
            new_args_list.append(a_val)
        new_args_t = tuple(new_args_list)

        strat = _effective_inline_strategy(
            ctx.classification_for(expr.symbol_id),
            must_inline=ctx.boundary_policy.inline_local_helpers,
        )
        if strat != InlineStrategy.DO_NOT_INLINE and expr.symbol_id in ctx.defs:
            if depth > ctx.max_depth:
                raise ParseError(f"Inlining depth exceeded for {expr.name!r}")
            fdef = ctx.defs[expr.symbol_id]

            if strat == InlineStrategy.EXPR_INLINE:
                frag = _expr_inline(fdef, new_args_t, ctx, depth + 1)
            elif strat == InlineStrategy.BLOCK_INLINE:
                arg_binds, atom_refs = _atomize_args(new_args_t, ctx.alloc)
                pre.extend(arg_binds)
                frag = _block_inline(fdef, tuple(atom_refs), ctx.alloc)
            else:
                raise ParseError(f"Unknown strategy: {strat}")

            # Recursively rewrite BLOCK_INLINE preludes to inline nested calls.
            if frag.prelude:
                prelude_block = NBlock(stmts=frag.prelude)
                _register_nested_defs(prelude_block, ctx)
                rewritten = _rewrite_block(prelude_block, ctx)
                if rewritten.defs or rewritten.stmts:
                    pre.append(rewritten)
            if len(frag.results) == 1:
                return pre, frag.results[0]
            if len(frag.results) == 0:
                # Zero-return helper — effects are in prelude, no result value.
                return pre, NConst(0)
            raise ParseError(
                f"Multi-return call to {expr.name!r} in single-value context"
            )
        return pre, NLocalCall(
            symbol_id=expr.symbol_id, name=expr.name, args=new_args_t
        )

    if isinstance(expr, NTopLevelCall):
        pre = []
        new_args_list = []
        for a in expr.args:
            a_pre, a_val = _inline_in_expr_with_prelude(a, ctx, depth)
            pre.extend(a_pre)
            new_args_list.append(a_val)
        new_args_t = tuple(new_args_list)
        sid = ctx.top_level_name_to_sid.get(expr.name)
        if sid is not None and sid in ctx.defs:
            strat = _effective_inline_strategy(
                ctx.classification_for(sid),
                must_inline=(expr.name in ctx.boundary_policy.inline_top_level_helpers),
            )
            if strat != InlineStrategy.DO_NOT_INLINE:
                if depth > ctx.max_depth:
                    raise ParseError(f"Inlining depth exceeded for {expr.name!r}")
                fdef = ctx.defs[sid]
                if strat == InlineStrategy.EXPR_INLINE:
                    frag = _expr_inline(fdef, new_args_t, ctx, depth + 1)
                elif strat == InlineStrategy.BLOCK_INLINE:
                    arg_binds, atom_refs = _atomize_args(new_args_t, ctx.alloc)
                    pre.extend(arg_binds)
                    frag = _block_inline(fdef, tuple(atom_refs), ctx.alloc)
                else:
                    raise ParseError(f"Unknown strategy: {strat}")
                if frag.prelude:
                    prelude_block = NBlock(stmts=frag.prelude)
                    _register_nested_defs(prelude_block, ctx)
                    rewritten = _rewrite_block(prelude_block, ctx)
                    if rewritten.defs or rewritten.stmts:
                        pre.append(rewritten)
                if len(frag.results) == 1:
                    return pre, frag.results[0]
                if len(frag.results) == 0:
                    return pre, NConst(0)
                raise ParseError(
                    f"Multi-return call to {expr.name!r} in single-value context"
                )
        return pre, NTopLevelCall(name=expr.name, args=new_args_t)

    if isinstance(expr, NUnresolvedCall):
        pre = []
        new_args_list = []
        for a in expr.args:
            a_pre, a_val = _inline_in_expr_with_prelude(a, ctx, depth)
            pre.extend(a_pre)
            new_args_list.append(a_val)
        return pre, NUnresolvedCall(name=expr.name, args=tuple(new_args_list))

    if isinstance(expr, NIte):
        c_pre, c_val = _inline_in_expr_with_prelude(expr.cond, ctx, depth)
        t_pre, t_val = _inline_in_expr_with_prelude(expr.if_true, ctx, depth)
        f_pre, f_val = _inline_in_expr_with_prelude(expr.if_false, ctx, depth)
        # NIte branches must not produce statement preludes — they execute
        # unconditionally here, so any side effects would be unsound.
        if t_pre or f_pre:
            raise ParseError(
                "NIte branch produced statement prelude during inlining. "
                "Branch sub-expressions must be pure (no BLOCK_INLINE)."
            )
        return c_pre, NIte(cond=c_val, if_true=t_val, if_false=f_val)

    assert_never(expr)


# ---------------------------------------------------------------------------
# Block-level rewrite (recursive IR-to-IR transform)
# ---------------------------------------------------------------------------


def _rewrite_block(block: NBlock, ctx: _InlineCtx) -> NBlock:
    stmts: list[NStmt] = []
    for stmt in block.stmts:
        stmts.extend(_rewrite_stmt(stmt, ctx))
    return NBlock(defs=block.defs, stmts=tuple(stmts))


def _rewrite_stmt(stmt: NStmt, ctx: _InlineCtx) -> list[NStmt]:
    if isinstance(stmt, (NBind, NAssign)):
        return _rewrite_bind_or_assign(stmt, ctx)

    if isinstance(stmt, NExprEffect):
        # Check for inlineable call as expression-statement.
        inline_sid: SymbolId | None = None
        if isinstance(stmt.expr, NLocalCall):
            inline_sid = stmt.expr.symbol_id
        elif isinstance(stmt.expr, NTopLevelCall):
            inline_sid = ctx.top_level_name_to_sid.get(stmt.expr.name)
        if inline_sid is not None:
            strat = ctx.strategy_for(inline_sid)
            fdef = ctx.defs.get(inline_sid)
            if strat != InlineStrategy.DO_NOT_INLINE and fdef is not None:
                # Inline the call and emit prelude + discard result.
                pre, val = _inline_in_expr_with_prelude(stmt.expr, ctx, 0)
                if pre:
                    return pre
                # No prelude, no return value (zero-return pure helper).
                if isinstance(val, (NConst, NRef)):
                    return []
                return [NExprEffect(expr=val)]
        pre, val = _inline_in_expr_with_prelude(stmt.expr, ctx, 0)
        out: list[NStmt] = list(pre)
        out.append(NExprEffect(expr=val))
        return out

    if isinstance(stmt, NIf):
        c_pre, c_val = _inline_in_expr_with_prelude(stmt.condition, ctx, 0)
        if c_pre:
            raise ParseError(
                "Control-flow condition requires statement prelude after helper "
                "inlining. NIf conditions must remain expression-only."
            )
        return [NIf(condition=c_val, then_body=_rewrite_block(stmt.then_body, ctx))]

    if isinstance(stmt, NSwitch):
        d_pre, d_val = _inline_in_expr_with_prelude(stmt.discriminant, ctx, 0)
        if d_pre:
            raise ParseError(
                "Control-flow condition requires statement prelude after helper "
                "inlining. NSwitch discriminants must remain expression-only."
            )
        new_cases = tuple(
            NSwitchCase(value=c.value, body=_rewrite_block(c.body, ctx))
            for c in stmt.cases
        )
        new_default = (
            _rewrite_block(stmt.default, ctx) if stmt.default is not None else None
        )
        out = list(d_pre)
        out.append(NSwitch(discriminant=d_val, cases=new_cases, default=new_default))
        return out

    if isinstance(stmt, NFor):
        cond_pre, cond_val = _inline_in_expr_with_prelude(stmt.condition, ctx, 0)
        # Prelude goes into condition_setup so it runs every iteration.
        existing_setup = stmt.condition_setup
        if cond_pre or existing_setup:
            setup_stmts: list[NStmt] = []
            if existing_setup:
                setup_stmts.extend(existing_setup.stmts)
            setup_stmts.extend(cond_pre)
            cond_setup = NBlock(
                defs=existing_setup.defs if existing_setup is not None else (),
                stmts=tuple(setup_stmts),
            )
        else:
            cond_setup = None
        return [
            NFor(
                init=_rewrite_block(stmt.init, ctx),
                condition=cond_val,
                condition_setup=cond_setup,
                post=_rewrite_block(stmt.post, ctx),
                body=_rewrite_block(stmt.body, ctx),
            )
        ]

    if isinstance(stmt, NLeave):
        return [stmt]

    if isinstance(stmt, NBlock):
        return [_rewrite_block(stmt, ctx)]

    assert_never(stmt)


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
    direct_sid: SymbolId | None = None
    direct_args: tuple[NExpr, ...] | None = None
    direct_name: str | None = None
    if isinstance(expr, NLocalCall) and expr.symbol_id in ctx.defs:
        direct_sid = expr.symbol_id
        direct_args = expr.args
        direct_name = expr.name
    elif isinstance(expr, NTopLevelCall):
        top_sid = ctx.top_level_name_to_sid.get(expr.name)
        if top_sid is not None and top_sid in ctx.defs:
            direct_sid = top_sid
            direct_args = expr.args
            direct_name = expr.name

    if direct_sid is not None and direct_args is not None and direct_name is not None:
        strat = _effective_inline_strategy(
            ctx.classification_for(direct_sid),
            must_inline=(
                ctx.boundary_policy.inline_local_helpers
                if isinstance(expr, NLocalCall)
                else (
                    isinstance(expr, NTopLevelCall)
                    and expr.name in ctx.boundary_policy.inline_top_level_helpers
                )
            ),
        )
        fdef = ctx.defs[direct_sid]

        if strat != InlineStrategy.DO_NOT_INLINE:
            # Inline arguments (may produce prelude), then atomize.
            arg_pre: list[NStmt] = []
            raw_args_list: list[NExpr] = []
            for a in direct_args:
                a_p, a_v = _inline_in_expr_with_prelude(a, ctx, 0)
                arg_pre.extend(a_p)
                raw_args_list.append(a_v)
            raw_args = tuple(raw_args_list)
            arg_binds, atom_refs = _atomize_args(raw_args, ctx.alloc)

            # Get InlineFragment from the appropriate strategy.
            frag: InlineFragment
            if strat == InlineStrategy.EXPR_INLINE:
                frag = _expr_inline(fdef, tuple(atom_refs), ctx, 1)
            elif strat == InlineStrategy.BLOCK_INLINE:
                frag = _block_inline(fdef, tuple(atom_refs), ctx.alloc)
            else:
                raise ParseError(f"Unknown strategy: {strat}")

            # For BLOCK_INLINE, the prelude may contain nested inlineable
            # calls (e.g. EXPR_INLINE helpers inside the cloned body).
            # Register freshened nested defs, then rewrite the prelude.
            prelude_stmts = list(frag.prelude)
            if prelude_stmts:
                prelude_block = NBlock(stmts=tuple(prelude_stmts))
                _register_nested_defs(prelude_block, ctx)
                rewritten_prelude = _rewrite_block(prelude_block, ctx)
                prelude_stmts = (
                    [rewritten_prelude]
                    if rewritten_prelude.defs or rewritten_prelude.stmts
                    else []
                )

            out: list[NStmt] = arg_pre + list(arg_binds) + prelude_stmts

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

    # Not a direct inlineable call: inline within expression (may produce prelude).
    pre, new_expr = _inline_in_expr_with_prelude(expr, ctx, 0)
    result: list[NStmt] = list(pre)
    result.append(
        cls_type(targets=stmt.targets, target_names=stmt.target_names, expr=new_expr)
    )
    return result


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def inline_pure_helpers(
    func: NormalizedFunction,
    *,
    extra_local_defs: dict[SymbolId, NFunctionDef] | None = None,
    top_level_inline_defs: dict[str, NFunctionDef] | None = None,
    allowed_model_calls: frozenset[str] = frozenset(),
    boundary_policy: InlineBoundaryPolicy | None = None,
) -> NormalizedFunction:
    """Inline helpers according to their classification strategy.

    1. Classify all nested helpers
    2. Pre-normalize switch → if in pure/block-inline helper bodies
    3. Recursively rewrite the body
    """
    defs: dict[SymbolId, NFunctionDef] = {
        fdef.symbol_id: fdef for fdef in collect_function_defs(func.body)
    }
    if extra_local_defs is not None:
        defs.update(extra_local_defs)

    top_level_name_to_sid: dict[str, SymbolId] = {}
    if top_level_inline_defs is not None:
        for name, fdef in top_level_inline_defs.items():
            defs[fdef.symbol_id] = fdef
            top_level_name_to_sid[name] = fdef.symbol_id

    max_id = max_symbol_id(func)
    for fdef in defs.values():
        max_id = max(max_id, max_symbol_id(fdef))
    alloc = SymbolAllocator(max_id + 1)

    summaries: dict[SymbolId, FunctionSummary] = {}
    for sid, fdef in defs.items():
        summaries[sid] = summarize_function(
            fdef.body,
            top_level_inline_sids=top_level_name_to_sid,
            allowed_model_calls=allowed_model_calls,
        )
    classifications = classify_helpers(summaries)
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

    ctx = _InlineCtx(
        defs=defs,
        classifications=classifications,
        alloc=alloc,
        top_level_name_to_sid=top_level_name_to_sid,
        allowed_model_calls=allowed_model_calls,
        boundary_policy=boundary_policy,
    )
    new_body = _rewrite_block(func.body, ctx)

    return NormalizedFunction(
        name=func.name,
        params=func.params,
        param_names=func.param_names,
        returns=func.returns,
        return_names=func.return_names,
        body=new_body,
    )
