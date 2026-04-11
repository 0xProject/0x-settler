from __future__ import annotations

import re
from collections import Counter
from typing import Callable, assert_never

from model_config import ModelConfig, TranslationPipeline
from model_helpers import _collect_model_binders, _expr_size, _expr_vars, _replace_expr
from model_ir import (
    Assignment,
    Call,
    ConditionalBlock,
    ConditionalBranch,
    Expr,
    FunctionModel,
    Ite,
    ModelStatement,
    Project,
)
from model_validate import validate_function_model


def _prune_dead_assignments(
    model: FunctionModel,
) -> FunctionModel:
    """Drop dead pure assignments from a model to avoid unused Lean lets."""

    def _prune_assignment_block(
        assignments: tuple[ModelStatement, ...],
        live_out: set[str],
    ) -> tuple[tuple[ModelStatement, ...], set[str]]:
        live = set(live_out)
        kept_rev: list[ModelStatement] = []
        for stmt in reversed(assignments):
            if isinstance(stmt, Assignment):
                if stmt.target not in live:
                    continue
                live.remove(stmt.target)
                live.update(_expr_vars(stmt.expr))
                kept_rev.append(stmt)
            elif isinstance(stmt, ConditionalBlock):
                for var in stmt.output_vars:
                    live.discard(var)
                live.update(_expr_vars(stmt.condition))
                kept_rev.append(stmt)
        kept_rev.reverse()
        return tuple(kept_rev), live

    live = set(model.return_names)
    kept_rev: list[ModelStatement] = []

    for stmt in reversed(model.assignments):
        if isinstance(stmt, Assignment):
            if stmt.target not in live:
                continue
            live.remove(stmt.target)
            live.update(_expr_vars(stmt.expr))
            kept_rev.append(stmt)
            continue

        if not isinstance(stmt, ConditionalBlock):
            assert_never(stmt)

        needed_indices = tuple(
            idx for idx, output in enumerate(stmt.output_vars) if output in live
        )
        needed_outputs = tuple(stmt.output_vars[idx] for idx in needed_indices)
        if not needed_outputs:
            continue

        then_out_live: set[str] = set()
        for idx in needed_indices:
            then_out_live.update(_expr_vars(stmt.then_branch.outputs[idx]))
        then_assignments, then_live = _prune_assignment_block(
            stmt.then_branch.assignments,
            then_out_live,
        )

        else_out_live: set[str] = set()
        for idx in needed_indices:
            else_out_live.update(_expr_vars(stmt.else_branch.outputs[idx]))
        else_assignments, else_live = _prune_assignment_block(
            stmt.else_branch.assignments,
            else_out_live,
        )

        live.difference_update(needed_outputs)
        live.update(_expr_vars(stmt.condition))
        live.update(then_live)
        live.update(else_live)

        kept_rev.append(
            ConditionalBlock(
                condition=stmt.condition,
                output_vars=needed_outputs,
                then_branch=ConditionalBranch(
                    assignments=then_assignments,
                    outputs=tuple(
                        stmt.then_branch.outputs[idx] for idx in needed_indices
                    ),
                ),
                else_branch=ConditionalBranch(
                    assignments=else_assignments,
                    outputs=tuple(
                        stmt.else_branch.outputs[idx] for idx in needed_indices
                    ),
                ),
            )
        )

    kept_rev.reverse()
    result = FunctionModel(
        fn_name=model.fn_name,
        assignments=tuple(kept_rev),
        param_names=model.param_names,
        return_names=model.return_names,
    )
    validate_function_model(result)
    return result

def _make_cse_gensym(model: FunctionModel) -> Callable[[], str]:
    max_cse = 0
    for binder in _collect_model_binders(model):
        match = re.fullmatch(r"_cse_(\d+)", binder)
        if match:
            max_cse = max(max_cse, int(match.group(1)))
    next_cse = max_cse + 1

    def _gensym() -> str:
        nonlocal next_cse
        name = f"_cse_{next_cse}"
        next_cse += 1
        return name

    return _gensym


def _is_component_wrapped_model_call(
    node: Expr, model_call_names: frozenset[str]
) -> bool:
    return (
        isinstance(node, Project)
        and isinstance(node.inner, Call)
        and node.inner.name in model_call_names
    )


def _walk_model_calls(
    node: Expr, model_call_names: frozenset[str], counts: Counter[Expr]
) -> None:
    if isinstance(node, Project):
        if _is_component_wrapped_model_call(node, model_call_names):
            counts[node] += 1
            assert isinstance(node.inner, Call)
            for arg in node.inner.args:
                _walk_model_calls(arg, model_call_names, counts)
            return
        _walk_model_calls(node.inner, model_call_names, counts)
    elif isinstance(node, Ite):
        _walk_model_calls(node.cond, model_call_names, counts)
        _walk_model_calls(node.if_true, model_call_names, counts)
        _walk_model_calls(node.if_false, model_call_names, counts)
    elif isinstance(node, Call):
        if node.name in model_call_names:
            counts[node] += 1
        for arg in node.args:
            _walk_model_calls(arg, model_call_names, counts)


def _replace_branch(
    branch: ConditionalBranch,
    replacements: dict[Expr, str],
) -> ConditionalBranch:
    return ConditionalBranch(
        assignments=tuple(
            _replace_statement(stmt, replacements) for stmt in branch.assignments
        ),
        outputs=tuple(_replace_expr(expr, replacements) for expr in branch.outputs),
    )


def _replace_statement(
    stmt: ModelStatement,
    replacements: dict[Expr, str],
) -> ModelStatement:
    if isinstance(stmt, Assignment):
        return Assignment(
            target=stmt.target,
            expr=_replace_expr(stmt.expr, replacements),
        )
    if isinstance(stmt, ConditionalBlock):
        return ConditionalBlock(
            condition=_replace_expr(stmt.condition, replacements),
            output_vars=stmt.output_vars,
            then_branch=_replace_branch(stmt.then_branch, replacements),
            else_branch=_replace_branch(stmt.else_branch, replacements),
        )
    assert_never(stmt)


def _is_hoistable_model_expr(
    expr: Expr,
    *,
    model_call_names: frozenset[str],
) -> bool:
    if isinstance(expr, Call):
        return expr.name in model_call_names
    return _is_component_wrapped_model_call(expr, model_call_names=model_call_names)


def _count_block_level_model_calls(
    stmts: tuple[ModelStatement, ...],
    *,
    outputs: tuple[Expr, ...] = (),
    model_call_names: frozenset[str],
) -> Counter[Expr]:
    counts: Counter[Expr] = Counter()
    for stmt in stmts:
        if isinstance(stmt, Assignment):
            _walk_model_calls(stmt.expr, model_call_names, counts)
        elif isinstance(stmt, ConditionalBlock):
            _walk_model_calls(stmt.condition, model_call_names, counts)
        else:
            assert_never(stmt)
    for expr in outputs:
        _walk_model_calls(expr, model_call_names, counts)
    return counts


def _build_hoist_bindings(
    counts: Counter[Expr],
    *,
    scope: set[str],
    model_call_names: frozenset[str],
    gensym: Callable[[], str],
) -> tuple[list[Assignment], dict[Expr, str]]:
    hoistable = [
        node
        for node, count in counts.items()
        if count > 1
        and _expr_vars(node).issubset(scope)
        and _is_hoistable_model_expr(node, model_call_names=model_call_names)
    ]
    hoistable.sort(key=_expr_size)

    replacements: dict[Expr, str] = {}
    hoisted: list[Assignment] = []
    for call in hoistable:
        name = gensym()
        expr = _replace_expr(call, replacements)
        hoisted.append(Assignment(target=name, expr=expr))
        replacements[call] = name
    return hoisted, replacements


def _hoist_calls_in_branch(
    branch: ConditionalBranch,
    *,
    scope: set[str],
    model_call_names: frozenset[str],
    gensym: Callable[[], str],
) -> ConditionalBranch:
    counts = _count_block_level_model_calls(
        branch.assignments,
        outputs=branch.outputs,
        model_call_names=model_call_names,
    )
    hoisted, replacements = _build_hoist_bindings(
        counts,
        scope=scope,
        model_call_names=model_call_names,
        gensym=gensym,
    )
    rewritten_assignments = _rewrite_hoisted_block(
        branch.assignments,
        scope=scope,
        model_call_names=model_call_names,
        hoisted=hoisted,
        replacements=replacements,
        gensym=gensym,
    )
    rewritten_outputs = (
        tuple(_replace_expr(expr, replacements) for expr in branch.outputs)
        if replacements
        else branch.outputs
    )
    return ConditionalBranch(
        assignments=rewritten_assignments,
        outputs=rewritten_outputs,
    )


def _rewrite_hoisted_block(
    stmts: tuple[ModelStatement, ...],
    *,
    scope: set[str],
    model_call_names: frozenset[str],
    hoisted: list[Assignment],
    replacements: dict[Expr, str],
    gensym: Callable[[], str],
) -> tuple[ModelStatement, ...]:
    local_scope = set(scope)
    for assignment in hoisted:
        local_scope.add(assignment.target)

    result: list[ModelStatement] = list(hoisted)
    for stmt in stmts:
        rewritten = _replace_statement(stmt, replacements) if replacements else stmt
        if isinstance(rewritten, ConditionalBlock):
            rewritten = ConditionalBlock(
                condition=rewritten.condition,
                output_vars=rewritten.output_vars,
                then_branch=_hoist_calls_in_branch(
                    rewritten.then_branch,
                    scope=local_scope,
                    model_call_names=model_call_names,
                    gensym=gensym,
                ),
                else_branch=_hoist_calls_in_branch(
                    rewritten.else_branch,
                    scope=local_scope,
                    model_call_names=model_call_names,
                    gensym=gensym,
                ),
            )
            local_scope.update(rewritten.output_vars)
        elif isinstance(rewritten, Assignment):
            local_scope.add(rewritten.target)
        result.append(rewritten)

    return tuple(result)


def _hoist_calls_in_block(
    stmts: tuple[ModelStatement, ...],
    *,
    scope: set[str],
    model_call_names: frozenset[str],
    gensym: Callable[[], str],
) -> tuple[ModelStatement, ...]:
    counts = _count_block_level_model_calls(stmts, model_call_names=model_call_names)
    hoisted, replacements = _build_hoist_bindings(
        counts,
        scope=scope,
        model_call_names=model_call_names,
        gensym=gensym,
    )
    return _rewrite_hoisted_block(
        stmts,
        scope=scope,
        model_call_names=model_call_names,
        hoisted=hoisted,
        replacements=replacements,
        gensym=gensym,
    )


def hoist_repeated_model_calls(
    model: FunctionModel,
    *,
    model_call_names: frozenset[str],
) -> FunctionModel:
    """Hoist repeated pure model-call sub-expressions into let-bindings."""
    gensym = _make_cse_gensym(model)
    new_stmts = _hoist_calls_in_block(
        model.assignments,
        scope=set(model.param_names),
        model_call_names=model_call_names,
        gensym=gensym,
    )

    result = FunctionModel(
        fn_name=model.fn_name,
        assignments=new_stmts,
        param_names=model.param_names,
        return_names=model.return_names,
    )
    validate_function_model(result)
    return result


def apply_optional_model_transforms(
    models: list[FunctionModel],
    config: ModelConfig,
    *,
    pipeline: TranslationPipeline,
) -> list[FunctionModel]:
    transformed = list(models)

    if pipeline.hoist_repeated_calls and config.hoist_repeated_calls:
        model_call_names = frozenset(config.function_order)
        transformed = [
            (
                hoist_repeated_model_calls(
                    model,
                    model_call_names=model_call_names,
                )
                if model.fn_name in config.hoist_repeated_calls
                else model
            )
            for model in transformed
        ]

    if pipeline.prune_dead_assignments:
        transformed = [
            (
                _prune_dead_assignments(model)
                if model.fn_name not in config.skip_prune
                else model
            )
            for model in transformed
        ]

    return transformed
