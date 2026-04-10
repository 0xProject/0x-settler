"""
Selection-aware staged translation pipeline.

This module owns orchestration from:
selection plan -> normalized IR -> simplification -> validation ->
restricted IR -> FunctionModel

It deliberately keeps selection, simplification, validation, and the
restricted→model bridge in separate layers.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from norm_simplify import simplify_function_def, simplify_normalized
from norm_validate import validate_restricted_boundary
from staged_selection import (
    FunctionKey,
    SelectedTargetInfo,
    SelectionPlan,
    build_selection_plan,
)

from norm_inline import InlineBoundaryPolicy, SymbolAllocator, inline_pure_helpers
from norm_ir import (
    NBlock,
    NExpr,
    NFunctionDef,
    NLocalCall,
    NormalizedFunction,
    NStmt,
    NTopLevelCall,
)
from norm_walk import map_expr
from restricted_ir import RestrictedFunction
from restricted_to_model import to_function_models
from yul_ast import (
    Block,
    BlockStmt,
    ForStmt,
    FunctionDef,
    FunctionDefStmt,
    IfStmt,
    ParseError,
    SwitchStmt,
    SymbolId,
)
from yul_normalize import normalize_function
from yul_parser import SyntaxParser
from yul_resolve import ResolutionResult, resolve_module

if TYPE_CHECKING:
    from yul_to_lean import FunctionModel, ModelConfig


@dataclass(frozen=True)
class _SyntaxFunctionInfo:
    func: FunctionDef
    group_idx: int
    lexical_path: tuple[str, ...]
    top_level_token_idx: int
    top_level_name: str


def translate_selected_models(
    yul_text: str,
    config: ModelConfig,
    *,
    selected_functions: tuple[str, ...] | None = None,
) -> list[FunctionModel]:
    """Run the new staged translation path for the selected targets."""

    plan = build_selection_plan(
        yul_text,
        config,
        selected_functions=selected_functions,
    )

    resolved_groups = [
        resolve_module(list(funcs), builtins=_staged_builtins())
        for funcs in plan.parsed_groups
    ]
    syntax_indexes = [
        _index_group_functions(group_idx, funcs)
        for group_idx, funcs in enumerate(plan.parsed_groups)
    ]

    restricted_by_sol_name: dict[str, RestrictedFunction] = {}
    for sol_name in plan.selected_functions:
        target_info = plan.target_infos[sol_name]
        syntax_index = syntax_indexes[target_info.key.group_idx]
        target_syntax = syntax_index[target_info.key.token_idx]
        outer_result = resolved_groups[target_info.key.group_idx][
            target_syntax.top_level_name
        ]

        target_nf = simplify_normalized(
            normalize_function(target_syntax.func, outer_result)
        )

        local_selected_map = _build_local_selected_map(
            plan,
            sol_name,
            outer_result,
            syntax_index,
        )
        top_level_selected_map = _build_top_level_selected_map(
            plan, target_info.key.group_idx
        )

        extra_local_defs, top_level_inline_defs = _build_inline_defs(
            target_info,
            plan,
            syntax_index,
            resolved_groups[target_info.key.group_idx],
        )

        target_nf = _rewrite_selected_calls(
            target_nf,
            local_selected_map=local_selected_map,
            top_level_selected_map=top_level_selected_map,
        )
        extra_local_defs = {
            sid: _rewrite_selected_calls_in_fdef(
                simplify_function_def(fdef),
                local_selected_map=local_selected_map,
                top_level_selected_map=top_level_selected_map,
            )
            for sid, fdef in extra_local_defs.items()
        }
        top_level_inline_defs = {
            name: _rewrite_selected_calls_in_fdef(
                simplify_function_def(fdef),
                local_selected_map=local_selected_map,
                top_level_selected_map=top_level_selected_map,
            )
            for name, fdef in top_level_inline_defs.items()
        }

        target_nf = inline_pure_helpers(
            target_nf,
            extra_local_defs=extra_local_defs,
            top_level_inline_defs=top_level_inline_defs,
            allowed_model_calls=frozenset(plan.selected_functions),
            boundary_policy=InlineBoundaryPolicy(
                inline_local_helpers=True,
                inline_top_level_helpers=frozenset(top_level_inline_defs),
            ),
        )
        target_nf = simplify_normalized(target_nf)

        from norm_constprop import propagate_constants
        from norm_memory import lower_memory
        from norm_to_restricted import lower_to_restricted

        target_nf = propagate_constants(target_nf)
        target_nf = simplify_normalized(target_nf)
        validate_restricted_boundary(
            target_nf,
            allowed_model_calls=frozenset(plan.selected_functions),
            allow_memory_ops=True,
        )
        target_nf = lower_memory(target_nf)
        target_nf = simplify_normalized(target_nf)
        validate_restricted_boundary(
            target_nf,
            allowed_model_calls=frozenset(plan.selected_functions),
        )
        restricted_by_sol_name[sol_name] = lower_to_restricted(target_nf)

    models_by_name = to_function_models(
        restricted_by_sol_name,
        extra_reserved_binder_names=_generated_model_def_names(
            plan.selected_functions,
            config,
        ),
    )
    return [models_by_name[sol_name] for sol_name in plan.selected_functions]


def _staged_builtins() -> frozenset[str]:
    from yul_to_lean import _EVM_BUILTINS

    return _EVM_BUILTINS


def _generated_model_def_names(
    selected_functions: tuple[str, ...],
    config: ModelConfig,
) -> frozenset[str]:
    names: set[str] = set()
    for sol_name in selected_functions:
        base = config.model_names[sol_name]
        if sol_name not in config.skip_norm:
            names.add(base)
        names.add(f"{base}_evm")
    return frozenset(names)


def _index_group_functions(
    group_idx: int,
    funcs: tuple[FunctionDef, ...],
) -> dict[int, _SyntaxFunctionInfo]:
    out: dict[int, _SyntaxFunctionInfo] = {}
    for func in funcs:
        _index_function(
            func,
            group_idx=group_idx,
            lexical_path=(func.name,),
            top_level_token_idx=func.span.start,
            top_level_name=func.name,
            out=out,
        )
    return out


def _index_function(
    func: FunctionDef,
    *,
    group_idx: int,
    lexical_path: tuple[str, ...],
    top_level_token_idx: int,
    top_level_name: str,
    out: dict[int, _SyntaxFunctionInfo],
) -> None:
    out[func.span.start] = _SyntaxFunctionInfo(
        func=func,
        group_idx=group_idx,
        lexical_path=lexical_path,
        top_level_token_idx=top_level_token_idx,
        top_level_name=top_level_name,
    )
    _index_block(
        func.body,
        group_idx=group_idx,
        lexical_path=lexical_path,
        top_level_token_idx=top_level_token_idx,
        top_level_name=top_level_name,
        out=out,
    )


def _index_block(
    block: Block,
    *,
    group_idx: int,
    lexical_path: tuple[str, ...],
    top_level_token_idx: int,
    top_level_name: str,
    out: dict[int, _SyntaxFunctionInfo],
) -> None:
    for stmt in block.stmts:
        if isinstance(stmt, FunctionDefStmt):
            _index_function(
                stmt.func,
                group_idx=group_idx,
                lexical_path=lexical_path + (stmt.func.name,),
                top_level_token_idx=top_level_token_idx,
                top_level_name=top_level_name,
                out=out,
            )
        elif isinstance(stmt, BlockStmt):
            _index_block(
                stmt.block,
                group_idx=group_idx,
                lexical_path=lexical_path,
                top_level_token_idx=top_level_token_idx,
                top_level_name=top_level_name,
                out=out,
            )
        elif isinstance(stmt, IfStmt):
            _index_block(
                stmt.body,
                group_idx=group_idx,
                lexical_path=lexical_path,
                top_level_token_idx=top_level_token_idx,
                top_level_name=top_level_name,
                out=out,
            )
        elif isinstance(stmt, SwitchStmt):
            for case in stmt.cases:
                _index_block(
                    case.body,
                    group_idx=group_idx,
                    lexical_path=lexical_path,
                    top_level_token_idx=top_level_token_idx,
                    top_level_name=top_level_name,
                    out=out,
                )
            if stmt.default is not None:
                _index_block(
                    stmt.default.body,
                    group_idx=group_idx,
                    lexical_path=lexical_path,
                    top_level_token_idx=top_level_token_idx,
                    top_level_name=top_level_name,
                    out=out,
                )
        elif isinstance(stmt, ForStmt):
            for sub in (stmt.init, stmt.post, stmt.body):
                _index_block(
                    sub,
                    group_idx=group_idx,
                    lexical_path=lexical_path,
                    top_level_token_idx=top_level_token_idx,
                    top_level_name=top_level_name,
                    out=out,
                )


def _build_local_selected_map(
    plan: SelectionPlan,
    sol_name: str,
    outer_result: ResolutionResult,
    syntax_index: dict[int, _SyntaxFunctionInfo],
) -> dict[SymbolId, str]:
    current = plan.target_infos[sol_name]
    mapping: dict[SymbolId, str] = {}
    for other_sol, other in plan.target_infos.items():
        if other.key.group_idx != current.key.group_idx:
            continue
        if other.top_level_key != current.top_level_key:
            continue
        if len(other.lexical_path) == 1:
            continue
        other_func = syntax_index[other.key.token_idx].func
        mapping[outer_result.declarations[other_func.name_span]] = other_sol
    return mapping


def _build_top_level_selected_map(
    plan: SelectionPlan,
    group_idx: int,
) -> dict[str, str]:
    mapping: dict[str, str] = {}
    for sol_name, info in plan.target_infos.items():
        if info.key.group_idx != group_idx:
            continue
        if info.key != info.top_level_key:
            continue
        mapping[info.raw_name] = sol_name
    return mapping


def _build_inline_defs(
    target_info: SelectedTargetInfo,
    plan: SelectionPlan,
    syntax_index: dict[int, _SyntaxFunctionInfo],
    resolved_group: dict[str, ResolutionResult],
) -> tuple[dict[SymbolId, NFunctionDef], dict[str, NFunctionDef]]:
    max_existing = 0
    for result in resolved_group.values():
        for sid in result.symbols:
            max_existing = max(max_existing, sid._id)
    alloc = SymbolAllocator(max_existing + 1)

    local_defs: dict[SymbolId, NFunctionDef] = {}
    top_level_defs: dict[str, NFunctionDef] = {}
    seen: set[FunctionKey] = set()
    for helper_key in target_info.helper_keys:
        if helper_key in seen:
            continue
        seen.add(helper_key)
        helper_info = syntax_index[helper_key.token_idx]
        outer_result = resolved_group[helper_info.top_level_name]
        helper_nf = normalize_function(helper_info.func, outer_result)
        if helper_key.token_idx == helper_info.top_level_token_idx:
            sid = alloc.alloc()
            top_level_defs[helper_info.func.name] = _prepare_helper_for_inlining(
                NFunctionDef(
                    name=helper_nf.name,
                    symbol_id=sid,
                    params=helper_nf.params,
                    param_names=helper_nf.param_names,
                    returns=helper_nf.returns,
                    return_names=helper_nf.return_names,
                    body=helper_nf.body,
                )
            )
        else:
            sid = outer_result.declarations[helper_info.func.name_span]
            local_defs[sid] = _prepare_helper_for_inlining(
                NFunctionDef(
                    name=helper_nf.name,
                    symbol_id=sid,
                    params=helper_nf.params,
                    param_names=helper_nf.param_names,
                    returns=helper_nf.returns,
                    return_names=helper_nf.return_names,
                    body=helper_nf.body,
                )
            )
    return local_defs, top_level_defs


def _prepare_helper_for_inlining(fdef: NFunctionDef) -> NFunctionDef:
    from norm_constprop import propagate_constants

    simplified = simplify_function_def(fdef)
    nf = NormalizedFunction(
        name=simplified.name,
        params=simplified.params,
        param_names=simplified.param_names,
        returns=simplified.returns,
        return_names=simplified.return_names,
        body=simplified.body,
    )
    nf = propagate_constants(nf)
    nf = simplify_normalized(nf)
    return NFunctionDef(
        name=nf.name,
        symbol_id=fdef.symbol_id,
        params=nf.params,
        param_names=nf.param_names,
        returns=nf.returns,
        return_names=nf.return_names,
        body=nf.body,
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
    from norm_ir import (
        NAssign,
        NBind,
        NBlock,
        NExprEffect,
        NFor,
        NIf,
        NLeave,
        NStore,
        NSwitch,
        NSwitchCase,
    )

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

    out: list[NStmt] = []
    for stmt in block.stmts:
        if isinstance(stmt, NBind):
            out.append(
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
            out.append(
                NAssign(
                    targets=stmt.targets,
                    target_names=stmt.target_names,
                    expr=map_expr(stmt.expr, rewrite_expr),
                )
            )
        elif isinstance(stmt, NExprEffect):
            out.append(NExprEffect(expr=map_expr(stmt.expr, rewrite_expr)))
        elif isinstance(stmt, NStore):
            out.append(
                NStore(
                    addr=map_expr(stmt.addr, rewrite_expr),
                    value=map_expr(stmt.value, rewrite_expr),
                )
            )
        elif isinstance(stmt, NIf):
            out.append(
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
            out.append(
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
            out.append(
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
            out.append(
                _rewrite_selected_calls_in_fdef(
                    stmt,
                    local_selected_map=local_selected_map,
                    top_level_selected_map=top_level_selected_map,
                )
            )
        elif isinstance(stmt, NBlock):
            out.append(
                _rewrite_selected_calls_in_block(
                    stmt,
                    local_selected_map=local_selected_map,
                    top_level_selected_map=top_level_selected_map,
                )
            )
        elif isinstance(stmt, NLeave):
            out.append(stmt)
        else:
            raise TypeError(f"Unexpected normalized statement {type(stmt).__name__}")
    from norm_ir import NBlock

    return NBlock(tuple(out))
