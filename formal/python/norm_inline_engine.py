"""Recursive helper-inlining engine for normalized IR."""

from __future__ import annotations

import enum
from dataclasses import dataclass
from typing import Callable, Literal, assert_never

from .norm_classify import InlineClassification, InlineStrategy
from .norm_inline_catalog import InlineCatalog
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
from .norm_walk import (
    SymbolAllocator,
    const_value,
    freshen_function_subtree,
    map_expr,
    map_stmt,
    simplify_ite,
)
from .yul_ast import LoweringError, SymbolId


@dataclass(frozen=True)
class InlineFragment:
    """Result of inlining a helper call."""

    prelude: tuple[NStmt, ...]
    results: tuple[NExpr, ...]


@dataclass(frozen=True)
class InlineBoundaryPolicy:
    """Call-survival policy for one inlining run."""

    inline_local_helpers: bool = False
    inline_top_level_helpers: frozenset[str] = frozenset()


@dataclass(frozen=True)
class InlineSession:
    """Mutable per-run state shared across recursive rewrites."""

    alloc: SymbolAllocator
    boundary_policy: InlineBoundaryPolicy = InlineBoundaryPolicy()
    max_depth: int = 40


@dataclass(frozen=True)
class ExprRewrite:
    """Expression rewrite result: setup statements plus the rewritten expression."""

    prelude: tuple[NStmt, ...]
    expr: NExpr


@dataclass(frozen=True)
class CallRewrite:
    """Call-site rewrite result used by expressions and statements."""

    prelude: tuple[NStmt, ...]
    residual_expr: NExpr | None
    results: tuple[NExpr, ...] | None

    @classmethod
    def residual(cls, *, prelude: tuple[NStmt, ...], expr: NExpr) -> CallRewrite:
        return cls(prelude=prelude, residual_expr=expr, results=None)

    @classmethod
    def expanded(
        cls,
        *,
        prelude: tuple[NStmt, ...],
        results: tuple[NExpr, ...],
    ) -> CallRewrite:
        return cls(prelude=prelude, residual_expr=None, results=results)


class CallAction(enum.Enum):
    """What the engine should do with one helper call site."""

    LEAVE_LIVE = "leave_live"
    EXPR_INLINE = "expr_inline"
    BLOCK_INLINE = "block_inline"
    STRICT_PREVIEW = "strict_preview"


@dataclass(frozen=True)
class ResolvedHelperCall:
    """Resolved helper call plus policy/classification metadata."""

    sid: SymbolId
    name: str
    kind: Literal["local", "top_level"]
    args: tuple[NExpr, ...]
    fdef: NFunctionDef | None
    classification: InlineClassification | None
    must_eliminate_call: bool

    @property
    def helper_kind_label(self) -> str:
        if self.kind == "local":
            return "local helper"
        return "top-level helper"

    def rebuild_expr(self) -> NExpr:
        if self.kind == "local":
            return NLocalCall(symbol_id=self.sid, name=self.name, args=self.args)
        return NTopLevelCall(name=self.name, args=self.args)


PreviewCallFn = Callable[[ResolvedHelperCall, int], InlineFragment]


class InlineEngine:
    """Rewrite a normalized function by inlining helper calls."""

    def __init__(
        self,
        catalog: InlineCatalog,
        session: InlineSession,
        *,
        preview_call: PreviewCallFn | None = None,
    ) -> None:
        self.catalog = catalog
        self.session = session
        self.preview_call = preview_call

    def rewrite_function(self, func: NormalizedFunction) -> NormalizedFunction:
        return NormalizedFunction(
            name=func.name,
            params=func.params,
            param_names=func.param_names,
            returns=func.returns,
            return_names=func.return_names,
            body=self.rewrite_block(func.body),
        )

    def rewrite_block(self, block: NBlock) -> NBlock:
        stmts: list[NStmt] = []
        for stmt in block.stmts:
            stmts.extend(self._rewrite_stmt(stmt))
        return NBlock(defs=block.defs, stmts=tuple(stmts))

    def _rewrite_stmt(self, stmt: NStmt) -> list[NStmt]:
        if isinstance(stmt, (NBind, NAssign)):
            return self._rewrite_bind_or_assign(stmt)

        if isinstance(stmt, NExprEffect):
            if isinstance(stmt.expr, (NLocalCall, NTopLevelCall)):
                return self._materialize_effect_stmt(
                    self._rewrite_call(stmt.expr, depth=0)
                )
            rewritten = self._rewrite_expr(stmt.expr, depth=0)
            return [*rewritten.prelude, NExprEffect(expr=rewritten.expr)]

        if isinstance(stmt, NIf):
            condition = self._rewrite_expr(stmt.condition, depth=0)
            if condition.prelude:
                raise LoweringError(
                    "Control-flow condition requires statement prelude after helper "
                    "inlining. NIf conditions must remain expression-only."
                )
            return [
                NIf(
                    condition=condition.expr,
                    then_body=self.rewrite_block(stmt.then_body),
                )
            ]

        if isinstance(stmt, NSwitch):
            discriminant = self._rewrite_expr(stmt.discriminant, depth=0)
            if discriminant.prelude:
                raise LoweringError(
                    "Control-flow condition requires statement prelude after helper "
                    "inlining. NSwitch discriminants must remain expression-only."
                )
            return [
                NSwitch(
                    discriminant=discriminant.expr,
                    cases=tuple(
                        NSwitchCase(
                            value=case.value, body=self.rewrite_block(case.body)
                        )
                        for case in stmt.cases
                    ),
                    default=(
                        self.rewrite_block(stmt.default)
                        if stmt.default is not None
                        else None
                    ),
                )
            ]

        if isinstance(stmt, NFor):
            condition = self._rewrite_expr(stmt.condition, depth=0)
            existing_setup = stmt.condition_setup
            if condition.prelude or existing_setup:
                setup_stmts: list[NStmt] = []
                if existing_setup is not None:
                    setup_stmts.extend(existing_setup.stmts)
                setup_stmts.extend(condition.prelude)
                condition_setup = NBlock(
                    defs=existing_setup.defs if existing_setup is not None else (),
                    stmts=tuple(setup_stmts),
                )
            else:
                condition_setup = None
            return [
                NFor(
                    init=self.rewrite_block(stmt.init),
                    condition=condition.expr,
                    condition_setup=condition_setup,
                    post=self.rewrite_block(stmt.post),
                    body=self.rewrite_block(stmt.body),
                )
            ]

        if isinstance(stmt, NLeave):
            return [stmt]

        if isinstance(stmt, NBlock):
            return [self.rewrite_block(stmt)]

        assert_never(stmt)

    def _rewrite_bind_or_assign(self, stmt: NBind | NAssign) -> list[NStmt]:
        expr = stmt.expr
        if isinstance(stmt, NBind) and expr is None:
            return [stmt]

        assert expr is not None
        if isinstance(expr, (NLocalCall, NTopLevelCall)):
            return self._materialize_bind_or_assign(
                stmt,
                self._rewrite_call(expr, depth=0),
            )

        rewritten = self._rewrite_expr(expr, depth=0)
        stmt_type = NBind if isinstance(stmt, NBind) else NAssign
        return [
            *rewritten.prelude,
            stmt_type(
                targets=stmt.targets,
                target_names=stmt.target_names,
                expr=rewritten.expr,
            ),
        ]

    def _rewrite_expr(self, expr: NExpr, *, depth: int) -> ExprRewrite:
        if isinstance(expr, (NConst, NRef)):
            return ExprRewrite(prelude=(), expr=expr)

        if isinstance(expr, NBuiltinCall):
            return self._rewrite_variadic_expr(
                expr.args,
                build=lambda args: NBuiltinCall(op=expr.op, args=args),
                depth=depth,
            )

        if isinstance(expr, (NLocalCall, NTopLevelCall)):
            rewritten = self._rewrite_call(expr, depth=depth)
            if rewritten.residual_expr is not None:
                return ExprRewrite(
                    prelude=rewritten.prelude,
                    expr=rewritten.residual_expr,
                )

            assert rewritten.results is not None
            if len(rewritten.results) == 0:
                return ExprRewrite(prelude=rewritten.prelude, expr=NConst(0))
            if len(rewritten.results) == 1:
                return ExprRewrite(
                    prelude=rewritten.prelude,
                    expr=rewritten.results[0],
                )
            raise LoweringError(
                f"Multi-return call to {expr.name!r} in single-value context"
            )

        if isinstance(expr, NUnresolvedCall):
            return self._rewrite_variadic_expr(
                expr.args,
                build=lambda args: NUnresolvedCall(name=expr.name, args=args),
                depth=depth,
            )

        if isinstance(expr, NIte):
            cond = self._rewrite_expr(expr.cond, depth=depth)
            if_true = self._rewrite_expr(expr.if_true, depth=depth)
            if_false = self._rewrite_expr(expr.if_false, depth=depth)
            if if_true.prelude or if_false.prelude:
                raise LoweringError(
                    "NIte branch produced statement prelude during inlining. "
                    "Branch sub-expressions must be pure (no BLOCK_INLINE)."
                )
            return ExprRewrite(
                prelude=cond.prelude,
                expr=NIte(
                    cond=cond.expr,
                    if_true=if_true.expr,
                    if_false=if_false.expr,
                ),
            )

        assert_never(expr)

    def _rewrite_variadic_expr(
        self,
        args: tuple[NExpr, ...],
        *,
        build: Callable[[tuple[NExpr, ...]], NExpr],
        depth: int,
    ) -> ExprRewrite:
        prelude: list[NStmt] = []
        rewritten_args: list[NExpr] = []
        for arg in args:
            rewritten = self._rewrite_expr(arg, depth=depth)
            prelude.extend(rewritten.prelude)
            rewritten_args.append(rewritten.expr)
        return ExprRewrite(prelude=tuple(prelude), expr=build(tuple(rewritten_args)))

    def _rewrite_call(
        self,
        expr: NLocalCall | NTopLevelCall,
        *,
        depth: int,
    ) -> CallRewrite:
        arg_prelude: list[NStmt] = []
        rewritten_args: list[NExpr] = []
        for arg in expr.args:
            rewritten = self._rewrite_expr(arg, depth=depth)
            arg_prelude.extend(rewritten.prelude)
            rewritten_args.append(rewritten.expr)
        rewritten_args_t = tuple(rewritten_args)

        call = self._resolve_helper_call(expr, rewritten_args_t)
        if call is None:
            residual: NExpr
            if isinstance(expr, NLocalCall):
                residual = NLocalCall(
                    symbol_id=expr.symbol_id,
                    name=expr.name,
                    args=rewritten_args_t,
                )
            else:
                residual = NTopLevelCall(name=expr.name, args=rewritten_args_t)
            return CallRewrite.residual(
                prelude=tuple(arg_prelude),
                expr=residual,
            )

        action = self._plan_call_action(call)
        if action == CallAction.LEAVE_LIVE:
            return CallRewrite.residual(
                prelude=tuple(arg_prelude),
                expr=call.rebuild_expr(),
            )

        fragment = self._expand_call(call, action, depth=depth + 1)
        prelude = list(arg_prelude)
        prelude.extend(self._rewrite_fragment_prelude(fragment.prelude))
        return CallRewrite.expanded(
            prelude=tuple(prelude),
            results=fragment.results,
        )

    def _resolve_helper_call(
        self,
        expr: NLocalCall | NTopLevelCall,
        rewritten_args: tuple[NExpr, ...],
    ) -> ResolvedHelperCall | None:
        if isinstance(expr, NLocalCall):
            sid = expr.symbol_id
            return ResolvedHelperCall(
                sid=sid,
                name=expr.name,
                kind="local",
                args=rewritten_args,
                fdef=self.catalog.defs.get(sid),
                classification=self.catalog.classifications.get(sid),
                must_eliminate_call=self.session.boundary_policy.inline_local_helpers,
            )

        top_level_sid = self.catalog.top_level_name_to_sid.get(expr.name)
        if top_level_sid is None:
            return None
        return ResolvedHelperCall(
            sid=top_level_sid,
            name=expr.name,
            kind="top_level",
            args=rewritten_args,
            fdef=self.catalog.defs.get(top_level_sid),
            classification=self.catalog.classifications.get(top_level_sid),
            must_eliminate_call=(
                expr.name in self.session.boundary_policy.inline_top_level_helpers
            ),
        )

    def _plan_call_action(self, call: ResolvedHelperCall) -> CallAction:
        classification = call.classification
        if classification is None:
            return (
                CallAction.STRICT_PREVIEW
                if call.must_eliminate_call
                else CallAction.LEAVE_LIVE
            )

        strategy = classification.strategy
        if (
            strategy == InlineStrategy.BLOCK_INLINE
            and classification.is_deferred
            and not call.must_eliminate_call
        ):
            return CallAction.LEAVE_LIVE
        if strategy == InlineStrategy.EXPR_INLINE:
            return CallAction.EXPR_INLINE
        if strategy == InlineStrategy.BLOCK_INLINE:
            return CallAction.BLOCK_INLINE
        return (
            CallAction.STRICT_PREVIEW
            if call.must_eliminate_call
            else CallAction.LEAVE_LIVE
        )

    def _expand_call(
        self,
        call: ResolvedHelperCall,
        action: CallAction,
        *,
        depth: int,
    ) -> InlineFragment:
        if depth > self.session.max_depth:
            raise LoweringError(f"Inlining depth exceeded for {call.name!r}")

        if action == CallAction.STRICT_PREVIEW:
            if self.preview_call is None:
                raise self._cannot_eliminate_error(call)
            return self.preview_call(call, depth)

        if call.fdef is None:
            raise LoweringError(
                f"Cannot inline {call.helper_kind_label} call {call.name!r}: "
                "missing helper definition."
            )

        if action == CallAction.EXPR_INLINE:
            return self._expr_inline(call.fdef, call.args, depth=depth)

        if action == CallAction.BLOCK_INLINE:
            binds, refs = atomize_args(call.args, self.session.alloc)
            fragment = self._block_inline(call.fdef, refs)
            return InlineFragment(
                prelude=binds + fragment.prelude,
                results=fragment.results,
            )

        raise LoweringError(f"Unknown call action: {action}")

    def _rewrite_fragment_prelude(
        self, prelude: tuple[NStmt, ...]
    ) -> tuple[NStmt, ...]:
        if not prelude:
            return ()
        prelude_block = NBlock(stmts=prelude)
        overlay = self.catalog.extend_with_freshened(prelude_block)
        nested_session = InlineSession(
            alloc=self.session.alloc,
            boundary_policy=InlineBoundaryPolicy(),
            max_depth=self.session.max_depth,
        )
        rewritten = InlineEngine(
            overlay,
            nested_session,
            preview_call=self.preview_call,
        ).rewrite_block(prelude_block)
        if not rewritten.defs and not rewritten.stmts:
            return ()
        return (rewritten,)

    def _materialize_effect_stmt(self, rewritten: CallRewrite) -> list[NStmt]:
        out = list(rewritten.prelude)
        if rewritten.residual_expr is not None:
            out.append(NExprEffect(expr=rewritten.residual_expr))
        return out

    def _materialize_bind_or_assign(
        self,
        stmt: NBind | NAssign,
        rewritten: CallRewrite,
    ) -> list[NStmt]:
        stmt_type = NBind if isinstance(stmt, NBind) else NAssign
        if rewritten.residual_expr is not None:
            return [
                *rewritten.prelude,
                stmt_type(
                    targets=stmt.targets,
                    target_names=stmt.target_names,
                    expr=rewritten.residual_expr,
                ),
            ]

        assert rewritten.results is not None
        if len(stmt.targets) != len(rewritten.results):
            raise LoweringError(
                f"Multi-return call in assignment to {len(stmt.targets)} target(s)"
            )

        out = list(rewritten.prelude)
        if len(stmt.targets) == 1:
            out.append(
                stmt_type(
                    targets=stmt.targets,
                    target_names=stmt.target_names,
                    expr=rewritten.results[0],
                )
            )
            return out

        temp_ids: list[SymbolId] = []
        for value in rewritten.results:
            tid = self.session.alloc.alloc()
            temp_ids.append(tid)
            out.append(
                NBind(
                    targets=(tid,),
                    target_names=(f"_tmp_{tid._id}",),
                    expr=value,
                )
            )
        for sid, name, tid in zip(stmt.targets, stmt.target_names, temp_ids):
            out.append(
                stmt_type(
                    targets=(sid,),
                    target_names=(name,),
                    expr=NRef(symbol_id=tid, name=f"_tmp_{tid._id}"),
                )
            )
        return out

    def _cannot_eliminate_error(self, call: ResolvedHelperCall) -> LoweringError:
        if call.fdef is None:
            return LoweringError(
                f"Cannot inline {call.helper_kind_label} call {call.name!r}: "
                "missing helper definition."
            )
        reason = (
            call.classification.unsupported_reason
            if call.classification is not None
            and call.classification.unsupported_reason is not None
            else "helper is not block-inlineable under the current classification"
        )
        return LoweringError(
            f"Cannot eliminate {call.helper_kind_label} call {call.name!r}: "
            f"{reason}."
        )

    def _expr_inline(
        self,
        fdef: NFunctionDef,
        args: tuple[NExpr, ...],
        *,
        depth: int,
    ) -> InlineFragment:
        subst: dict[SymbolId, NExpr] = {}
        for sid, arg in zip(fdef.params, args):
            subst[sid] = arg
        for sid in fdef.returns:
            subst[sid] = NConst(0)

        self._symex_block(fdef.body, subst, depth=depth)
        return InlineFragment(
            prelude=(),
            results=tuple(subst[sid] for sid in fdef.returns),
        )

    def _symex_block(
        self,
        block: NBlock,
        subst: dict[SymbolId, NExpr],
        *,
        depth: int,
    ) -> None:
        for stmt in block.stmts:
            self._symex_stmt(stmt, subst, depth=depth)

    def _symex_stmt(
        self,
        stmt: NStmt,
        subst: dict[SymbolId, NExpr],
        *,
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
                subst[stmt.targets[0]] = self._rewrite_pure_expr(resolved, depth=depth)
                return

            multi = self._try_inline_multi(resolved, depth=depth)
            if isinstance(multi, tuple) and len(multi) == len(stmt.targets):
                for sid, value in zip(stmt.targets, multi):
                    subst[sid] = value
                return
            raise LoweringError(
                "Multi-target assignment to non-inlineable call in ExprInline body "
                f"(targets: {len(stmt.targets)})"
            )

        if isinstance(stmt, NIf):
            cond = self._rewrite_pure_expr(
                substitute_nexpr(stmt.condition, subst),
                depth=depth,
            )
            cond_value = const_value(cond)
            if cond_value is not None:
                if cond_value != 0:
                    self._symex_block(stmt.then_body, subst, depth=depth)
                return
            if_subst = dict(subst)
            self._symex_block(stmt.then_body, if_subst, depth=depth)
            for sid, branch_value in if_subst.items():
                if branch_value is subst.get(sid):
                    continue
                pre_value = subst.get(sid, NConst(0))
                subst[sid] = simplify_ite(cond, branch_value, pre_value)
            return

        if isinstance(stmt, NBlock):
            self._symex_block(stmt, subst, depth=depth)
            return

        if isinstance(stmt, (NFor, NLeave, NExprEffect, NSwitch)):
            raise LoweringError(f"Unexpected {type(stmt).__name__} in ExprInline body")

        assert_never(stmt)

    def _rewrite_pure_expr(self, expr: NExpr, *, depth: int) -> NExpr:
        rewritten = self._rewrite_expr(expr, depth=depth)
        if rewritten.prelude:
            raise LoweringError(
                "Non-EXPR_INLINE call in pure expression context "
                "(requires statement prelude)"
            )
        return rewritten.expr

    def _try_inline_multi(
        self,
        expr: NExpr,
        *,
        depth: int,
    ) -> tuple[NExpr, ...] | NExpr:
        if not isinstance(expr, (NLocalCall, NTopLevelCall)):
            return expr
        call = self._resolve_helper_call(expr, expr.args)
        if call is None or call.classification is None:
            return expr
        if self._plan_call_action(call) != CallAction.EXPR_INLINE or call.fdef is None:
            return expr
        fragment = self._expr_inline(call.fdef, call.args, depth=depth + 1)
        if len(fragment.results) == 1:
            return fragment.results[0]
        return fragment.results

    def build_block_inline_preview(
        self,
        call: ResolvedHelperCall,
        *,
        depth: int,
    ) -> NormalizedFunction:
        """Build a preview function for strict helper-boundary checking."""
        if depth > self.session.max_depth:
            raise LoweringError(f"Inlining depth exceeded for {call.name!r}")
        if call.fdef is None:
            raise LoweringError(
                f"Cannot inline {call.helper_kind_label} call {call.name!r}: "
                "missing helper definition."
            )

        binds, refs = atomize_args(call.args, self.session.alloc)
        fragment = self._block_inline(call.fdef, refs)
        result_refs = tuple(
            result for result in fragment.results if isinstance(result, NRef)
        )
        if len(result_refs) != len(fragment.results):
            raise LoweringError(
                f"Cannot eliminate {call.helper_kind_label} call {call.name!r}: "
                "block-inline preview produced non-reference return values."
            )

        return NormalizedFunction(
            name=call.name,
            params=(),
            param_names=(),
            returns=tuple(ref.symbol_id for ref in result_refs),
            return_names=tuple(ref.name for ref in result_refs),
            body=NBlock(stmts=binds + fragment.prelude),
        )

    def _block_inline(
        self,
        fdef: NFunctionDef,
        atom_args: tuple[NRef, ...],
    ) -> InlineFragment:
        fresh = freshen_function_subtree(fdef, self.session.alloc)

        prelude: list[NStmt] = []
        ret_ids = fresh.returns
        for rid in ret_ids:
            prelude.append(
                NBind(
                    targets=(rid,),
                    target_names=(f"_ret_{rid._id}",),
                    expr=NConst(0),
                )
            )

        did_leave_id = self.session.alloc.alloc()
        prelude.append(
            NBind(
                targets=(did_leave_id,),
                target_names=(f"_did_leave_{did_leave_id._id}",),
                expr=NConst(0),
            )
        )

        param_subst: dict[SymbolId, NExpr] = {
            sid: arg for sid, arg in zip(fresh.params, atom_args)
        }
        cloned = self._clone_body_for_block_inline(
            fresh.body,
            param_subst=param_subst,
            did_leave_id=did_leave_id,
        )
        if cloned.defs or cloned.stmts:
            prelude.append(cloned)

        return InlineFragment(
            prelude=tuple(prelude),
            results=tuple(
                NRef(symbol_id=rid, name=f"_ret_{rid._id}") for rid in ret_ids
            ),
        )

    def _clone_body_for_block_inline(
        self,
        block: NBlock,
        *,
        param_subst: dict[SymbolId, NExpr],
        did_leave_id: SymbolId,
    ) -> NBlock:
        return lower_leave_block(self._subst_block(block, param_subst), did_leave_id)

    def _subst_block(self, block: NBlock, subst: dict[SymbolId, NExpr]) -> NBlock:
        if not subst:
            return block
        return NBlock(
            defs=block.defs,
            stmts=tuple(
                map_stmt(
                    stmt,
                    map_expr_fn=lambda expr: substitute_nexpr(expr, subst),
                    map_block_fn=lambda child: self._subst_block(child, subst),
                )
                for stmt in block.stmts
            ),
        )


def atomize_args(
    args: tuple[NExpr, ...],
    alloc: SymbolAllocator,
) -> tuple[tuple[NStmt, ...], tuple[NRef, ...]]:
    """Bind each argument to a fresh temp so the inlined helper sees atoms."""
    binds: list[NStmt] = []
    refs: list[NRef] = []
    for arg in args:
        if isinstance(arg, NRef):
            refs.append(arg)
            continue
        tid = alloc.alloc()
        name = f"_arg_{tid._id}"
        binds.append(NBind(targets=(tid,), target_names=(name,), expr=arg))
        refs.append(NRef(symbol_id=tid, name=name))
    return tuple(binds), tuple(refs)


def substitute_nexpr(
    expr: NExpr,
    subst: dict[SymbolId, NExpr],
) -> NExpr:
    """Replace ``NRef`` nodes according to *subst*."""

    def rewrite(node: NExpr) -> NExpr:
        if isinstance(node, NRef):
            return subst.get(node.symbol_id, node)
        return node

    return map_expr(expr, rewrite)
