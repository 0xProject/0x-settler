"""
Library entrypoint for Yul -> FunctionModel translation.

Owns the end-to-end pipeline: selection -> lowering -> model transforms.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from model_config import ModelConfig
from model_transforms import apply_optional_model_transforms
from model_validate import validate_model_set
from norm_constprop import propagate_constants
from norm_inline import InlineBoundaryPolicy, SymbolAllocator, inline_pure_helpers
from norm_ir import (
    NAssign,
    NBind,
    NBlock,
    NExpr,
    NExprEffect,
    NFor,
    NFunctionDef,
    NIf,
    NLeave,
    NLocalCall,
    NormalizedFunction,
    NStmt,
    NStore,
    NSwitch,
    NSwitchCase,
    NTopLevelCall,
)
from norm_memory import lower_memory
from norm_simplify import lower_leave, simplify_normalized
from norm_to_restricted import lower_to_restricted
from norm_validate import validate_restricted_boundary
from norm_walk import map_expr
from restricted_ir import RestrictedFunction
from restricted_to_model import to_function_models
from selection import (
    SelectedFunctionInfo,
    SelectedTargetInfo,
    SelectionPlan,
    build_selection_plan,
)
from yul_ast import ParseError, SymbolId
from yul_normalize import normalize_function

if TYPE_CHECKING:
    from model_ir import FunctionModel


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
    models = _translate_selected_models(selection_plan)
    models = apply_optional_model_transforms(
        models,
        config.transforms,
        model_call_names=frozenset(config.selection.function_order),
        optimize=optimize,
    )
    validate_model_set(models)
    return models


# ---------------------------------------------------------------------------
# Target lowering
# ---------------------------------------------------------------------------


def _translate_selected_models(plan: SelectionPlan) -> list[FunctionModel]:
    allowed_model_calls = frozenset(plan.selected_functions)
    restricted_by_name: dict[str, RestrictedFunction] = {}
    for sol_name in plan.selected_functions:
        restricted_by_name[sol_name] = _lower_target(
            target=plan.target_infos[sol_name],
            plan=plan,
            allowed_model_calls=allowed_model_calls,
        )

    models_by_name = to_function_models(restricted_by_name)
    return [models_by_name[sol_name] for sol_name in plan.selected_functions]


def _lower_target(
    *,
    target: SelectedTargetInfo,
    plan: SelectionPlan,
    allowed_model_calls: frozenset[str],
) -> RestrictedFunction:
    local_selected_map = _build_local_selected_map(plan, target)
    top_level_selected_map = _build_top_level_selected_map(plan, target.info.key.group_idx)

    normalized = normalize_function(target.info.func, target.info.resolution)
    normalized = _rewrite_selected_calls(
        normalized,
        local_selected_map=local_selected_map,
        top_level_selected_map=top_level_selected_map,
    )

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
        boundary_policy=InlineBoundaryPolicy(
            inline_local_helpers=True,
            inline_top_level_helpers=frozenset(top_level_defs),
        ),
    )

    normalized = simplify_normalized(normalized)
    normalized = lower_leave(normalized)
    normalized = propagate_constants(normalized)
    normalized = simplify_normalized(normalized)
    validate_restricted_boundary(
        normalized,
        allowed_model_calls=allowed_model_calls,
        allow_memory_ops=True,
    )
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
    for other_sol_name, other in plan.target_infos.items():
        if other_sol_name == target.sol_name:
            continue
        if other.info.key.group_idx != target.info.key.group_idx:
            continue
        if other.info.top_level_key != target.info.top_level_key:
            continue
        if len(other.info.lexical_path) == 1:
            continue
        mapping[target.info.resolution.declarations[other.info.func.name_span]] = other_sol_name
    return mapping


def _build_top_level_selected_map(
    plan: SelectionPlan,
    group_idx: int,
) -> dict[str, str]:
    mapping: dict[str, str] = {}
    for sol_name, target in plan.target_infos.items():
        if target.info.key.group_idx != group_idx:
            continue
        if target.info.key != target.info.top_level_key:
            continue
        mapping[target.info.raw_name] = sol_name
    return mapping


def _build_inline_defs(
    target: SelectedTargetInfo,
    *,
    local_selected_map: dict[SymbolId, str],
    top_level_selected_map: dict[str, str],
) -> tuple[dict[SymbolId, NFunctionDef], dict[str, NFunctionDef]]:
    max_existing = 0
    for sid in target.info.resolution.symbols:
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
    """Normalize, simplify, constprop, and rewrite a helper for inlining."""
    normalized = normalize_function(helper.func, helper.resolution)
    symbol_id = helper.resolution.declarations[helper.func.name_span]
    simplified = simplify_normalized(normalized)
    simplified = propagate_constants(simplified)
    simplified = simplify_normalized(simplified)
    fdef = NFunctionDef(
        name=simplified.name,
        symbol_id=symbol_id,
        params=simplified.params,
        param_names=simplified.param_names,
        returns=simplified.returns,
        return_names=simplified.return_names,
        body=simplified.body,
    )
    return _rewrite_selected_calls_in_fdef(
        fdef,
        local_selected_map=local_selected_map,
        top_level_selected_map=top_level_selected_map,
    )


def _rewrite_selected_calls(
    func: NormalizedFunction,
    *,
    local_selected_map: dict[SymbolId, str],
    top_level_selected_map: dict[str, str],
) -> NormalizedFunction:
    def rw(expr: NExpr) -> NExpr:
        if isinstance(expr, NLocalCall) and expr.symbol_id in local_selected_map:
            return NTopLevelCall(name=local_selected_map[expr.symbol_id], args=expr.args)
        if isinstance(expr, NTopLevelCall) and expr.name in top_level_selected_map:
            return NTopLevelCall(name=top_level_selected_map[expr.name], args=expr.args)
        return expr

    def rw_block(block: NBlock) -> NBlock:
        return NBlock(tuple(rw_stmt(s) for s in block.stmts))

    def rw_block_or_none(block: NBlock | None) -> NBlock | None:
        return rw_block(block) if block is not None else None

    def rw_stmt(stmt: NStmt) -> NStmt:
        if isinstance(stmt, NBind):
            return NBind(targets=stmt.targets, target_names=stmt.target_names,
                         expr=map_expr(stmt.expr, rw) if stmt.expr is not None else None)
        if isinstance(stmt, NAssign):
            return NAssign(targets=stmt.targets, target_names=stmt.target_names,
                           expr=map_expr(stmt.expr, rw))
        if isinstance(stmt, NExprEffect):
            return NExprEffect(expr=map_expr(stmt.expr, rw))
        if isinstance(stmt, NStore):
            return NStore(addr=map_expr(stmt.addr, rw), value=map_expr(stmt.value, rw))
        if isinstance(stmt, NIf):
            return NIf(condition=map_expr(stmt.condition, rw),
                       then_body=rw_block(stmt.then_body))
        if isinstance(stmt, NSwitch):
            return NSwitch(
                discriminant=map_expr(stmt.discriminant, rw),
                cases=tuple(NSwitchCase(value=c.value, body=rw_block(c.body))
                            for c in stmt.cases),
                default=rw_block_or_none(stmt.default))
        if isinstance(stmt, NFor):
            return NFor(init=rw_block(stmt.init), condition=map_expr(stmt.condition, rw),
                        condition_setup=rw_block_or_none(stmt.condition_setup),
                        post=rw_block(stmt.post), body=rw_block(stmt.body))
        if isinstance(stmt, NFunctionDef):
            return NFunctionDef(
                name=stmt.name, symbol_id=stmt.symbol_id, params=stmt.params,
                param_names=stmt.param_names, returns=stmt.returns,
                return_names=stmt.return_names, body=rw_block(stmt.body))
        if isinstance(stmt, NBlock):
            return rw_block(stmt)
        if isinstance(stmt, NLeave):
            return stmt
        raise ParseError(f"Unexpected normalized statement {type(stmt).__name__}")

    return NormalizedFunction(
        name=func.name, params=func.params, param_names=func.param_names,
        returns=func.returns, return_names=func.return_names,
        body=rw_block(func.body))


def _rewrite_selected_calls_in_fdef(
    fdef: NFunctionDef,
    *,
    local_selected_map: dict[SymbolId, str],
    top_level_selected_map: dict[str, str],
) -> NFunctionDef:
    rewritten = _rewrite_selected_calls(
        NormalizedFunction(
            name=fdef.name, params=fdef.params, param_names=fdef.param_names,
            returns=fdef.returns, return_names=fdef.return_names, body=fdef.body),
        local_selected_map=local_selected_map,
        top_level_selected_map=top_level_selected_map,
    )
    return NFunctionDef(
        name=rewritten.name, symbol_id=fdef.symbol_id, params=rewritten.params,
        param_names=rewritten.param_names, returns=rewritten.returns,
        return_names=rewritten.return_names, body=rewritten.body)
