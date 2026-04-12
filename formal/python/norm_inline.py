"""Public helper-inlining API for normalized IR."""

from __future__ import annotations

from .norm_inline_boundary import (
    build_inline_session,
    inline_helpers_to_boundary,
    seal_helper_boundary,
)
from .norm_inline_catalog import build_inline_catalog
from .norm_inline_engine import (
    InlineBoundaryPolicy,
    InlineEngine,
    InlineFragment,
)
from .norm_ir import NFunctionDef, NormalizedFunction
from .yul_ast import SymbolId


def inline_pure_helpers(
    func: NormalizedFunction,
    *,
    extra_local_defs: dict[SymbolId, NFunctionDef] | None = None,
    top_level_inline_defs: dict[str, NFunctionDef] | None = None,
    allowed_model_calls: frozenset[str] = frozenset(),
    boundary_policy: InlineBoundaryPolicy | None = None,
) -> NormalizedFunction:
    """Inline helpers according to their classification strategy."""
    catalog = build_inline_catalog(
        func,
        extra_local_defs=extra_local_defs,
        top_level_inline_defs=top_level_inline_defs,
        allowed_model_calls=allowed_model_calls,
    )
    session = build_inline_session(
        func,
        defs=catalog.defs,
        boundary_policy=boundary_policy,
    )
    return InlineEngine(catalog, session).rewrite_function(func)


__all__ = [
    "InlineBoundaryPolicy",
    "InlineFragment",
    "inline_helpers_to_boundary",
    "inline_pure_helpers",
    "seal_helper_boundary",
]
