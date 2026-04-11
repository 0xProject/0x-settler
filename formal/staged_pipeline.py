"""
Lower selected Yul targets to FunctionModel.
"""

from __future__ import annotations

from norm_simplify import lower_leave, simplify_function_def, simplify_normalized
from norm_validate import validate_restricted_boundary
from staged_selection import SelectedHelperInfo, SelectedTargetInfo, SelectionPlan

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
from norm_to_restricted import lower_to_restricted
from norm_walk import map_expr
from restricted_ir import RestrictedFunction
from restricted_to_model import to_function_models
from yul_ast import ParseError, SymbolId
from yul_normalize import normalize_function


def translate_selected_models(plan: SelectionPlan) -> list["FunctionModel"]:
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
    top_level_selected_map = _build_top_level_selected_map(plan, target.key.group_idx)

    normalized = normalize_function(target.func, target.resolution)
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


def _build_local_selected_map(
    plan: SelectionPlan,
    target: SelectedTargetInfo,
) -> dict[SymbolId, str]:
    mapping: dict[SymbolId, str] = {}
    for other_sol_name, other in plan.target_infos.items():
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
    for sol_name, target in plan.target_infos.items():
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
        helper_def = _prepare_helper_for_inlining(helper)
        helper_def = _rewrite_selected_calls_in_fdef(
            simplify_function_def(helper_def),
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


def _prepare_helper_for_inlining(helper: SelectedHelperInfo) -> NFunctionDef:
    normalized = normalize_function(helper.func, helper.resolution)
    return _prepare_function_def(
        NFunctionDef(
            name=normalized.name,
            symbol_id=helper.resolution.declarations[helper.func.name_span],
            params=normalized.params,
            param_names=normalized.param_names,
            returns=normalized.returns,
            return_names=normalized.return_names,
            body=normalized.body,
        )
    )


def _prepare_function_def(fdef: NFunctionDef) -> NFunctionDef:
    simplified = simplify_function_def(fdef)
    normalized = NormalizedFunction(
        name=simplified.name,
        params=simplified.params,
        param_names=simplified.param_names,
        returns=simplified.returns,
        return_names=simplified.return_names,
        body=simplified.body,
    )
    normalized = propagate_constants(normalized)
    normalized = simplify_normalized(normalized)
    return NFunctionDef(
        name=normalized.name,
        symbol_id=fdef.symbol_id,
        params=normalized.params,
        param_names=normalized.param_names,
        returns=normalized.returns,
        return_names=normalized.return_names,
        body=normalized.body,
    )


def _rewrite_selected_calls(
    func: NormalizedFunction,
    *,
    local_selected_map: dict[SymbolId, str],
    top_level_selected_map: dict[str, str],
) -> NormalizedFunction:
    return NormalizedFunction(
        name=func.name,
        params=func.params,
        param_names=func.param_names,
        returns=func.returns,
        return_names=func.return_names,
        body=_rewrite_selected_calls_in_block(
            func.body,
            local_selected_map=local_selected_map,
            top_level_selected_map=top_level_selected_map,
        ),
    )


def _rewrite_selected_calls_in_fdef(
    fdef: NFunctionDef,
    *,
    local_selected_map: dict[SymbolId, str],
    top_level_selected_map: dict[str, str],
) -> NFunctionDef:
    return NFunctionDef(
        name=fdef.name,
        symbol_id=fdef.symbol_id,
        params=fdef.params,
        param_names=fdef.param_names,
        returns=fdef.returns,
        return_names=fdef.return_names,
        body=_rewrite_selected_calls_in_block(
            fdef.body,
            local_selected_map=local_selected_map,
            top_level_selected_map=top_level_selected_map,
        ),
    )


def _rewrite_selected_calls_in_block(
    block: NBlock,
    *,
    local_selected_map: dict[SymbolId, str],
    top_level_selected_map: dict[str, str],
) -> NBlock:
    def rewrite_expr(expr: NExpr) -> NExpr:
        if isinstance(expr, NLocalCall) and expr.symbol_id in local_selected_map:
            return NTopLevelCall(
                name=local_selected_map[expr.symbol_id],
                args=expr.args,
            )
        if isinstance(expr, NTopLevelCall) and expr.name in top_level_selected_map:
            return NTopLevelCall(
                name=top_level_selected_map[expr.name],
                args=expr.args,
            )
        return expr

    rewritten: list[NStmt] = []
    for stmt in block.stmts:
        if isinstance(stmt, NBind):
            rewritten.append(
                NBind(
                    targets=stmt.targets,
                    target_names=stmt.target_names,
                    expr=(
                        map_expr(stmt.expr, rewrite_expr)
                        if stmt.expr is not None
                        else None
                    ),
                )
            )
        elif isinstance(stmt, NAssign):
            rewritten.append(
                NAssign(
                    targets=stmt.targets,
                    target_names=stmt.target_names,
                    expr=map_expr(stmt.expr, rewrite_expr),
                )
            )
        elif isinstance(stmt, NExprEffect):
            rewritten.append(NExprEffect(expr=map_expr(stmt.expr, rewrite_expr)))
        elif isinstance(stmt, NStore):
            rewritten.append(
                NStore(
                    addr=map_expr(stmt.addr, rewrite_expr),
                    value=map_expr(stmt.value, rewrite_expr),
                )
            )
        elif isinstance(stmt, NIf):
            rewritten.append(
                NIf(
                    condition=map_expr(stmt.condition, rewrite_expr),
                    then_body=_rewrite_selected_calls_in_block(
                        stmt.then_body,
                        local_selected_map=local_selected_map,
                        top_level_selected_map=top_level_selected_map,
                    ),
                )
            )
        elif isinstance(stmt, NSwitch):
            rewritten.append(
                NSwitch(
                    discriminant=map_expr(stmt.discriminant, rewrite_expr),
                    cases=tuple(
                        NSwitchCase(
                            value=case.value,
                            body=_rewrite_selected_calls_in_block(
                                case.body,
                                local_selected_map=local_selected_map,
                                top_level_selected_map=top_level_selected_map,
                            ),
                        )
                        for case in stmt.cases
                    ),
                    default=(
                        _rewrite_selected_calls_in_block(
                            stmt.default,
                            local_selected_map=local_selected_map,
                            top_level_selected_map=top_level_selected_map,
                        )
                        if stmt.default is not None
                        else None
                    ),
                )
            )
        elif isinstance(stmt, NFor):
            rewritten.append(
                NFor(
                    init=_rewrite_selected_calls_in_block(
                        stmt.init,
                        local_selected_map=local_selected_map,
                        top_level_selected_map=top_level_selected_map,
                    ),
                    condition=map_expr(stmt.condition, rewrite_expr),
                    condition_setup=(
                        _rewrite_selected_calls_in_block(
                            stmt.condition_setup,
                            local_selected_map=local_selected_map,
                            top_level_selected_map=top_level_selected_map,
                        )
                        if stmt.condition_setup is not None
                        else None
                    ),
                    post=_rewrite_selected_calls_in_block(
                        stmt.post,
                        local_selected_map=local_selected_map,
                        top_level_selected_map=top_level_selected_map,
                    ),
                    body=_rewrite_selected_calls_in_block(
                        stmt.body,
                        local_selected_map=local_selected_map,
                        top_level_selected_map=top_level_selected_map,
                    ),
                )
            )
        elif isinstance(stmt, NFunctionDef):
            rewritten.append(
                _rewrite_selected_calls_in_fdef(
                    stmt,
                    local_selected_map=local_selected_map,
                    top_level_selected_map=top_level_selected_map,
                )
            )
        elif isinstance(stmt, NBlock):
            rewritten.append(
                _rewrite_selected_calls_in_block(
                    stmt,
                    local_selected_map=local_selected_map,
                    top_level_selected_map=top_level_selected_map,
                )
            )
        elif isinstance(stmt, NLeave):
            rewritten.append(stmt)
        else:
            raise ParseError(f"Unexpected normalized statement {type(stmt).__name__}")
    return NBlock(tuple(rewritten))


from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from model_ir import FunctionModel
