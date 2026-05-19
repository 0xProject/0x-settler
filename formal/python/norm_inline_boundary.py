"""Strict helper-boundary enforcement for normalized-IR inlining."""

from __future__ import annotations

from .norm_classify import (
    FunctionSummary,
    UnsupportedKind,
    first_unsupported_kind,
    summarize_function,
    unsupported_kind_reason,
)
from .norm_constprop import simplify_normalized
from .norm_inline_catalog import InlineCatalog, build_inline_catalog
from .norm_inline_engine import (
    InlineBoundaryPolicy,
    InlineEngine,
    InlineFragment,
    InlineSession,
    ResolvedHelperCall,
)
from .norm_ir import NBlock, NFunctionDef, NormalizedFunction, NRef
from .norm_memory import lower_memory
from .norm_walk import (
    SymbolAllocator,
    collect_function_defs,
    first_runtime_local_call,
    max_symbol_id,
    strip_function_defs,
)
from .yul_ast import LoweringError, SymbolId


def inline_helpers_to_boundary(
    func: NormalizedFunction,
    *,
    extra_local_defs: dict[SymbolId, NFunctionDef] | None = None,
    top_level_inline_defs: dict[str, NFunctionDef] | None = None,
    allowed_model_calls: frozenset[str] = frozenset(),
    boundary_policy: InlineBoundaryPolicy,
    max_rounds: int = 8,
) -> NormalizedFunction:
    """Run strict helper elimination to a simplification fixed point."""
    current = func
    for _ in range(max_rounds):
        catalog = build_inline_catalog(
            current,
            extra_local_defs=extra_local_defs,
            top_level_inline_defs=top_level_inline_defs,
            allowed_model_calls=allowed_model_calls,
        )
        session = build_inline_session(
            current,
            defs=catalog.defs,
            boundary_policy=boundary_policy,
        )

        def preview(call: ResolvedHelperCall, depth: int) -> InlineFragment:
            return preview_specialized_call(
                call,
                catalog=catalog,
                session=session,
                depth=depth,
            )

        rewritten = InlineEngine(
            catalog,
            session,
            preview_call=preview,
        ).rewrite_function(current)
        simplified = simplify_normalized(rewritten)
        if simplified == current:
            return simplified
        current = simplified
    raise LoweringError(
        "Helper elimination did not converge before the helper boundary."
    )


def seal_helper_boundary(func: NormalizedFunction) -> NormalizedFunction:
    """Erase nested helper defs after runtime helper calls are gone."""
    residual_call = first_runtime_local_call(func.body)
    if residual_call is not None:
        raise LoweringError(
            f"Residual local helper call {residual_call.name!r} crossed the "
            "helper boundary. All runtime helper calls must be inlined "
            "before nested defs are erased."
        )
    if not collect_function_defs(func.body):
        return func
    return NormalizedFunction(
        name=func.name,
        params=func.params,
        param_names=func.param_names,
        returns=func.returns,
        return_names=func.return_names,
        body=strip_function_defs(func.body),
    )


def build_inline_session(
    func: NormalizedFunction,
    *,
    defs: dict[SymbolId, NFunctionDef],
    boundary_policy: InlineBoundaryPolicy | None = None,
) -> InlineSession:
    """Allocate fresh SymbolIds for one inlining run."""
    max_id = max_symbol_id(func)
    for fdef in defs.values():
        max_id = max(max_id, max_symbol_id(fdef))
    return InlineSession(
        alloc=SymbolAllocator(max_id + 1),
        boundary_policy=boundary_policy or InlineBoundaryPolicy(),
    )


def preview_specialized_call(
    call: ResolvedHelperCall,
    *,
    catalog: InlineCatalog,
    session: InlineSession,
    depth: int,
) -> InlineFragment:
    """Try call-site specialization before failing a strict helper boundary."""
    engine = InlineEngine(catalog, session)
    preview_func = engine.build_block_inline_preview(call, depth=depth)
    preview_func = simplify_normalized(preview_func)
    summary = summarize_preview_body(preview_func.body, catalog)
    if preview_can_retry_after_memory_lowering(summary):
        preview_func = lower_memory(preview_func)
        preview_func = simplify_normalized(preview_func)
        summary = summarize_preview_body(preview_func.body, catalog)
    blocker = first_unsupported_kind(summary)
    if blocker is not None:
        raise LoweringError(
            f"Cannot eliminate {call.helper_kind_label} call {call.name!r}: "
            f"{unsupported_kind_reason(blocker)}."
        )

    return InlineFragment(
        prelude=preview_func.body.stmts,
        results=tuple(
            NRef(symbol_id=sid, name=name)
            for sid, name in zip(preview_func.returns, preview_func.return_names)
        ),
    )


def summarize_preview_body(block: NBlock, catalog: InlineCatalog) -> FunctionSummary:
    return summarize_function(
        block,
        top_level_inline_sids=catalog.top_level_name_to_sid,
        allowed_model_calls=catalog.allowed_model_calls,
    )


def preview_can_retry_after_memory_lowering(summary: FunctionSummary) -> bool:
    blocker = first_unsupported_kind(summary)
    if not summary.reads_memory:
        return False
    return blocker is not None and blocker not in {
        UnsupportedKind.FOR_LOOP,
        UnsupportedKind.TOP_LEVEL_CALL,
        UnsupportedKind.UNRESOLVED_CALL,
    }
