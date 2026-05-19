"""Helper catalog construction for normalized-IR inlining."""

from __future__ import annotations

from dataclasses import dataclass

from .norm_classify import (
    InlineClassification,
    InlineStrategy,
    classify_helpers,
    summarize_function,
)
from .norm_ir import (
    NBlock,
    NBuiltinCall,
    NConst,
    NExpr,
    NFunctionDef,
    NIf,
    NormalizedFunction,
    NStmt,
    NSwitch,
)
from .norm_walk import collect_function_defs, map_function_def
from .yul_ast import SymbolId


@dataclass(frozen=True)
class InlineCatalog:
    """Immutable helper metadata for one inlining pass."""

    defs: dict[SymbolId, NFunctionDef]
    classifications: dict[SymbolId, InlineClassification]
    top_level_name_to_sid: dict[str, SymbolId]
    allowed_model_calls: frozenset[str]

    def extend_with_freshened(self, block: NBlock) -> InlineCatalog:
        """Return a derived catalog including freshened helper defs from *block*."""
        new_defs = tuple(collect_function_defs(block))
        if not new_defs:
            return self

        combined_defs = dict(self.defs)
        for fdef in new_defs:
            combined_defs[fdef.symbol_id] = fdef

        classifications = _classify_defs(
            combined_defs,
            top_level_name_to_sid=self.top_level_name_to_sid,
            allowed_model_calls=self.allowed_model_calls,
        )
        return InlineCatalog(
            defs=combined_defs,
            classifications=classifications,
            top_level_name_to_sid=self.top_level_name_to_sid,
            allowed_model_calls=self.allowed_model_calls,
        )


def build_inline_catalog(
    func: NormalizedFunction,
    *,
    extra_local_defs: dict[SymbolId, NFunctionDef] | None = None,
    top_level_inline_defs: dict[str, NFunctionDef] | None = None,
    allowed_model_calls: frozenset[str] = frozenset(),
) -> InlineCatalog:
    """Collect, classify, and normalize helper defs for one inlining run."""
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

    classifications = _classify_defs(
        defs,
        top_level_name_to_sid=top_level_name_to_sid,
        allowed_model_calls=allowed_model_calls,
    )

    normalized_defs = dict(defs)
    for sid, cls in classifications.items():
        if cls.strategy != InlineStrategy.EXPR_INLINE:
            continue
        old = normalized_defs[sid]
        normalized_defs[sid] = NFunctionDef(
            name=old.name,
            symbol_id=old.symbol_id,
            params=old.params,
            param_names=old.param_names,
            returns=old.returns,
            return_names=old.return_names,
            body=_pre_normalize_block(old.body),
        )

    return InlineCatalog(
        defs=normalized_defs,
        classifications=classifications,
        top_level_name_to_sid=top_level_name_to_sid,
        allowed_model_calls=allowed_model_calls,
    )


def _classify_defs(
    defs: dict[SymbolId, NFunctionDef],
    *,
    top_level_name_to_sid: dict[str, SymbolId],
    allowed_model_calls: frozenset[str],
) -> dict[SymbolId, InlineClassification]:
    summaries = {
        sid: summarize_function(
            fdef.body,
            top_level_inline_sids=top_level_name_to_sid,
            allowed_model_calls=allowed_model_calls,
        )
        for sid, fdef in defs.items()
    }
    return classify_helpers(summaries)


def _normalize_switch_to_if(stmt: NSwitch) -> NBlock:
    """Convert a pure helper switch into nested ifs for symbolic execution."""
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
