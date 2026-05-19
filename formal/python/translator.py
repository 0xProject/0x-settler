"""
Library entrypoint for Yul -> FunctionModel translation.

Owns the end-to-end pipeline: selection -> lowering -> model transforms.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, overload

from .model_config import ModelConfig
from .model_transforms import apply_optional_model_transforms
from .model_validate import validate_model_set
from .norm_constprop import simplify_normalized
from .norm_inline import (
    InlineBoundaryPolicy,
    inline_helpers_to_boundary,
    inline_pure_helpers,
    seal_helper_boundary,
)
from .norm_ir import (
    NBlock,
    NExpr,
    NFunctionDef,
    NLocalCall,
    NormalizedFunction,
    NTopLevelCall,
)
from .norm_leave import lower_leave
from .norm_memory import lower_memory
from .norm_to_restricted import lower_to_restricted
from .norm_validate import validate_restricted_boundary
from .norm_walk import SymbolAllocator, map_block, map_expr, map_function_def, map_stmt
from .restricted_ir import RestrictedFunction
from .restricted_to_model import to_function_models
from .selection import (
    SelectedFunctionInfo,
    SelectedTargetInfo,
    SelectionPlan,
    build_selection_plan,
)
from .yul_ast import SymbolId
from .yul_normalize import normalize_function

if TYPE_CHECKING:
    from .model_ir import FunctionModel


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def translate_yul_to_models(
    yul_text: str,
    config: ModelConfig,
    *,
    selected_functions: tuple[str, ...] | None = None,
    optimize: bool = True,
) -> list[FunctionModel]:
    selection_plan = build_selection_plan(
        yul_text,
        config.selection,
        selected_functions=selected_functions,
    )
    models = _translate_selected_models(selection_plan, config)
    models = apply_optional_model_transforms(
        models,
        config.transforms,
        model_call_names=frozenset(selection_plan.selected_functions),
        optimize=optimize,
    )
    validate_model_set(models)
    return models


# ---------------------------------------------------------------------------
# Target lowering
# ---------------------------------------------------------------------------


def _translate_selected_models(
    plan: SelectionPlan,
    config: ModelConfig,
) -> list[FunctionModel]:
    allowed_model_calls = frozenset(plan.selected_functions)
    restricted_by_name: dict[str, RestrictedFunction] = {}
    for sol_name in plan.selected_functions:
        restricted_by_name[sol_name] = _lower_target(
            target=plan.targets[sol_name],
            plan=plan,
            allowed_model_calls=allowed_model_calls,
        )

    models_by_name = to_function_models(
        restricted_by_name,
        emission=config.emission,
        transforms=config.transforms,
    )
    return [models_by_name[sol_name] for sol_name in plan.selected_functions]


def _lower_target(
    *,
    target: SelectedTargetInfo,
    plan: SelectionPlan,
    allowed_model_calls: frozenset[str],
) -> RestrictedFunction:
    local_selected_map = _build_local_selected_map(plan, target)
    top_level_selected_map = _build_top_level_selected_map(plan, target.key.group_idx)

    normalized = normalize_function(target.func, target.resolution)
    normalized = _rewrite_selected_calls(
        normalized,
        local_selected_map=local_selected_map,
        top_level_selected_map=top_level_selected_map,
    )
    normalized = simplify_normalized(normalized)

    local_defs, top_level_defs = _build_inline_defs(
        target,
        local_selected_map=local_selected_map,
        top_level_selected_map=top_level_selected_map,
    )
    normalized = inline_pure_helpers(
        normalized,
        extra_local_defs=local_defs,
        top_level_inline_defs=top_level_defs,
        allowed_model_calls=allowed_model_calls,
    )
    normalized = simplify_normalized(normalized)
    normalized = inline_helpers_to_boundary(
        normalized,
        extra_local_defs=local_defs,
        top_level_inline_defs=top_level_defs,
        allowed_model_calls=allowed_model_calls,
        boundary_policy=InlineBoundaryPolicy(
            inline_local_helpers=True,
            inline_top_level_helpers=frozenset(top_level_defs),
        ),
    )
    normalized = seal_helper_boundary(normalized)

    normalized = simplify_normalized(normalized)
    normalized = lower_leave(normalized)
    normalized = lower_memory(normalized)
    normalized = simplify_normalized(normalized)
    validate_restricted_boundary(
        normalized,
        allowed_model_calls=allowed_model_calls,
    )
    return lower_to_restricted(normalized)


# ---------------------------------------------------------------------------
# Selected-call rewriting helpers
# ---------------------------------------------------------------------------


def _build_local_selected_map(
    plan: SelectionPlan,
    target: SelectedTargetInfo,
) -> dict[SymbolId, str]:
    mapping: dict[SymbolId, str] = {}
    for other_sol_name, other in plan.targets.items():
        if other_sol_name == target.sol_name:
            continue
        if other.key.group_idx != target.key.group_idx:
            continue
        if other.top_level_key != target.top_level_key:
            continue
        if len(other.lexical_path) == 1:
            continue
        mapping[target.resolution.declarations[other.func.name_span]] = other_sol_name
    return mapping


def _build_top_level_selected_map(
    plan: SelectionPlan,
    group_idx: int,
) -> dict[str, str]:
    mapping: dict[str, str] = {}
    for sol_name, target in plan.targets.items():
        if target.key.group_idx != group_idx:
            continue
        if target.key != target.top_level_key:
            continue
        mapping[target.raw_name] = sol_name
    return mapping


def _build_inline_defs(
    target: SelectedTargetInfo,
    *,
    local_selected_map: dict[SymbolId, str],
    top_level_selected_map: dict[str, str],
) -> tuple[dict[SymbolId, NFunctionDef], dict[str, NFunctionDef]]:
    max_existing = 0
    for sid in target.resolution.symbols:
        max_existing = max(max_existing, sid._id)
    for helper in target.helper_infos:
        for sid in helper.resolution.symbols:
            max_existing = max(max_existing, sid._id)
    alloc = SymbolAllocator(max_existing + 1)

    local_defs: dict[SymbolId, NFunctionDef] = {}
    top_level_defs: dict[str, NFunctionDef] = {}
    for helper in target.helper_infos:
        helper_def = _prepare_helper(
            helper,
            local_selected_map=local_selected_map,
            top_level_selected_map=top_level_selected_map,
        )
        if helper.key == helper.top_level_key:
            top_level_defs[helper.raw_name] = NFunctionDef(
                name=helper_def.name,
                symbol_id=alloc.alloc(),
                params=helper_def.params,
                param_names=helper_def.param_names,
                returns=helper_def.returns,
                return_names=helper_def.return_names,
                body=helper_def.body,
            )
            continue
        local_defs[helper.resolution.declarations[helper.func.name_span]] = helper_def
    return local_defs, top_level_defs


def _prepare_helper(
    helper: SelectedFunctionInfo,
    *,
    local_selected_map: dict[SymbolId, str],
    top_level_selected_map: dict[str, str],
) -> NFunctionDef:
    """Normalize, simplify, and rewrite a helper for inlining."""
    normalized = normalize_function(helper.func, helper.resolution)
    symbol_id = helper.resolution.declarations[helper.func.name_span]
    optimized = simplify_normalized(normalized)
    fdef = NFunctionDef(
        name=optimized.name,
        symbol_id=symbol_id,
        params=optimized.params,
        param_names=optimized.param_names,
        returns=optimized.returns,
        return_names=optimized.return_names,
        body=optimized.body,
    )
    return _rewrite_selected_calls(
        fdef,
        local_selected_map=local_selected_map,
        top_level_selected_map=top_level_selected_map,
    )


@overload
def _rewrite_selected_calls(
    func: NormalizedFunction,
    *,
    local_selected_map: dict[SymbolId, str],
    top_level_selected_map: dict[str, str],
) -> NormalizedFunction: ...


@overload
def _rewrite_selected_calls(
    func: NFunctionDef,
    *,
    local_selected_map: dict[SymbolId, str],
    top_level_selected_map: dict[str, str],
) -> NFunctionDef: ...


def _rewrite_selected_calls(
    func: NormalizedFunction | NFunctionDef,
    *,
    local_selected_map: dict[SymbolId, str],
    top_level_selected_map: dict[str, str],
) -> NormalizedFunction | NFunctionDef:
    def rw(expr: NExpr) -> NExpr:
        if isinstance(expr, NLocalCall) and expr.symbol_id in local_selected_map:
            return NTopLevelCall(
                name=local_selected_map[expr.symbol_id], args=expr.args
            )
        if isinstance(expr, NTopLevelCall) and expr.name in top_level_selected_map:
            return NTopLevelCall(name=top_level_selected_map[expr.name], args=expr.args)
        return expr

    def rw_block(block: NBlock) -> NBlock:
        return map_block(
            block,
            map_function_def_fn=lambda fdef: map_function_def(
                fdef,
                map_block_fn=rw_block,
            ),
            map_stmt_fn=lambda stmt: map_stmt(
                stmt,
                map_expr_fn=lambda e: map_expr(e, rw),
                map_block_fn=rw_block,
            ),
        )

    new_body = rw_block(func.body)

    if isinstance(func, NFunctionDef):
        return NFunctionDef(
            name=func.name,
            symbol_id=func.symbol_id,
            params=func.params,
            param_names=func.param_names,
            returns=func.returns,
            return_names=func.return_names,
            body=new_body,
        )
    return NormalizedFunction(
        name=func.name,
        params=func.params,
        param_names=func.param_names,
        returns=func.returns,
        return_names=func.return_names,
        body=new_body,
    )
