"""
Shared target-selection stage for both the old and new translation paths.

This module owns:
- exact/raw function selection semantics
- scope-aware helper visibility collection
- token-based identity for selected targets and visible helpers

It intentionally does NOT own inlining, normalization, or model lowering.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from yul_ast import FunctionDef, ParseError
from yul_parser import SyntaxParser
from yul_resolve import resolve_module


def _span_size(item: tuple[int, FunctionDef]) -> int:
    """Sort key: span width of the FunctionDef in a (group_idx, func) pair."""
    return item[1].span.end - item[1].span.start


if TYPE_CHECKING:
    from yul_to_lean import CallResolution, ModelConfig, RejectedHelperMap, YulFunction


@dataclass(frozen=True)
class FunctionKey:
    """Opaque identity for a function definition within one lexical group."""

    group_idx: int
    token_idx: int


@dataclass(frozen=True)
class SelectedTargetInfo:
    """Selection metadata for one requested output model."""

    sol_name: str
    key: FunctionKey
    raw_name: str
    lexical_path: tuple[str, ...]
    top_level_key: FunctionKey
    helper_keys: tuple[FunctionKey, ...]


@dataclass(frozen=True)
class SelectionPlan:
    """Shared selection output consumed by both translation paths."""

    tokens: tuple[tuple[str, str], ...]
    parsed_groups: tuple[tuple[FunctionDef, ...], ...]
    selected_functions: tuple[str, ...]
    helper_tables: dict[str, dict[str, "YulFunction"]]
    rejected_helper_tables: dict[str, "RejectedHelperMap"]
    target_call_resolutions: dict[str, "CallResolution"]
    target_infos: dict[str, SelectedTargetInfo]


def _group_for_token(
    parsed_groups: tuple[tuple[FunctionDef, ...], ...],
    token_idx: int,
) -> int:
    matches: list[tuple[int, FunctionDef]] = []
    for group_idx, funcs in enumerate(parsed_groups):
        for func in funcs:
            if func.span.start <= token_idx < func.span.end:
                matches.append((group_idx, func))
    if not matches:
        raise ParseError(
            f"No enclosing function group found for token index {token_idx}"
        )
    matches.sort(key=_span_size)
    return matches[0][0]


def _top_level_for_token(
    parsed_groups: tuple[tuple[FunctionDef, ...], ...],
    token_idx: int,
) -> tuple[int, FunctionDef]:
    matches: list[tuple[int, FunctionDef]] = []
    for group_idx, funcs in enumerate(parsed_groups):
        for func in funcs:
            if func.span.start <= token_idx < func.span.end:
                matches.append((group_idx, func))
    if not matches:
        raise ParseError(
            f"No enclosing top-level function found for token index {token_idx}"
        )
    matches.sort(key=_span_size)
    return matches[0]


def build_selection_plan(
    yul_text: str,
    config: "ModelConfig",
    *,
    selected_functions: tuple[str, ...] | None = None,
) -> SelectionPlan:
    """Build the shared selection/helper-visibility plan for translation."""

    # Avoid importing yul_to_lean at module import time: yul_to_lean itself
    # uses this selection stage.
    import yul_to_lean as ytl

    tokens = tuple(ytl.tokenize_yul(yul_text))
    parsed_groups = tuple(
        tuple(g) for g in SyntaxParser(list(tokens)).parse_function_groups()
    )

    # Module-level pre-pass: validate cross-function scoping independently per
    # lexical group before any target selection occurs.
    for func_group in parsed_groups:
        resolve_module(list(func_group), builtins=ytl._EVM_BUILTINS)

    selected = (
        selected_functions if selected_functions is not None else config.function_order
    )

    resolver = ytl.YulParser(list(tokens))
    path_by_token_idx = {
        idx: path for idx, _name, path in resolver._walk_function_defs()
    }

    resolved_positions: dict[str, tuple[int, str, tuple[str, ...]]] = {}
    known_yul_names: set[str] = set()
    for sol_name in selected:
        parser = ytl.YulParser(list(tokens))
        if (
            config.exact_yul_names is not None
            and config.exact_yul_names.get(sol_name) is not None
        ):
            exact_yul_name = config.exact_yul_names[sol_name]
            exact_selector = ytl._parse_exact_yul_selector(exact_yul_name)
            n_params = config.n_params.get(sol_name) if config.n_params else None
            if exact_selector is None:
                matches = parser._find_exact_function_matches(
                    exact_yul_name,
                    n_params=n_params,
                    search_nested=True,
                )
            else:
                matches = [
                    (idx, path)
                    for idx, path in parser._find_exact_function_matches(
                        exact_selector[-1],
                        n_params=n_params,
                        search_nested=True,
                    )
                    if path == exact_selector
                ]
            if not matches:
                rendered = (
                    "::".join(exact_selector)
                    if exact_selector is not None
                    else exact_yul_name
                )
                if n_params is not None:
                    raise ParseError(
                        f"Exact Yul function {rendered!r} with {n_params} parameter(s) not found"
                    )
                raise ParseError(f"Exact Yul function path {rendered!r} not found")
            if len(matches) > 1:
                rendered = (
                    "::".join(exact_selector)
                    if exact_selector is not None
                    else exact_yul_name
                )
                raise ParseError(
                    f"Multiple exact Yul functions matched {rendered!r}. Refuse to guess."
                )
            token_idx, path = matches[0]
            resolved_positions[sol_name] = (token_idx, path[-1], path)
        else:
            n_params = config.n_params.get(sol_name) if config.n_params else None
            target_prefix = f"fun_{sol_name}_"
            matches3: list[tuple[int, str, tuple[str, ...]]] = [
                (idx, fn_name, path)
                for idx, fn_name, path in parser._walk_function_defs()
                if len(path) == 1
                and fn_name.startswith(target_prefix)
                and fn_name[len(target_prefix) :].isdigit()
            ]
            if not matches3:
                raise ParseError(
                    f"Yul function for '{sol_name}' not found "
                    f"(expected pattern fun_{sol_name}_<digits>)"
                )
            if n_params is not None:
                matches3 = [
                    (idx, fn_name, path)
                    for idx, fn_name, path in matches3
                    if parser._count_params_at(idx) == n_params
                ]
                if not matches3:
                    raise ParseError(
                        f"No Yul function for {sol_name!r} matches "
                        f"{n_params} parameter(s)"
                    )
            if known_yul_names and len(matches3) > 1:
                narrowed = parser._disambiguate_by_references(
                    [idx for idx, _name, _path in matches3],
                    known_yul_names,
                    sol_name in config.exclude_known,
                )
                narrowed_set = set(narrowed)
                matches3 = [
                    (idx, fn_name, path)
                    for idx, fn_name, path in matches3
                    if idx in narrowed_set
                ]
            if len(matches3) > 1:
                names = [fn_name for _idx, fn_name, _path in matches3]
                raise ParseError(
                    f"Multiple Yul functions match '{sol_name}': {names}. "
                    f"Rename wrapper functions to avoid collisions "
                    f"(e.g. prefix with 'wrap_')."
                )
            token_idx, raw_name, path = matches3[0]
            resolved_positions[sol_name] = (token_idx, raw_name, path)
        known_yul_names.add(resolved_positions[sol_name][1])

    protected_token_idxs = frozenset(
        token_idx
        for sol_name, (token_idx, _raw_name, _path) in resolved_positions.items()
        if config.exact_yul_names is not None
        and config.exact_yul_names.get(sol_name) is not None
    )

    all_selected_token_idxs: set[int] = set()
    token_idx_to_sol_name: dict[int, str] = {}
    for sol_name in selected:
        token_idx = resolved_positions[sol_name][0]
        all_selected_token_idxs.add(token_idx)
        token_idx_to_sol_name[token_idx] = sol_name

    helper_tables: dict[str, dict[str, ytl.YulFunction]] = {}
    rejected_helper_tables: dict[str, ytl.RejectedHelperMap] = {}
    target_call_resolutions: dict[str, ytl.CallResolution] = {}
    target_infos: dict[str, SelectedTargetInfo] = {}

    for sol_name in selected:
        fn_token_idx, raw_name, lexical_path = resolved_positions[sol_name]

        authoritative_token_idxs = {fn_token_idx}

        helper_table: dict[str, ytl.YulFunction] = {}
        rejected_helpers: ytl.RejectedHelperMap = {}

        scope_chain: list[tuple[int, int]] = []
        cur_idx = fn_token_idx
        while True:
            obj_start, obj_end = ytl._find_enclosing_block_range(list(tokens), cur_idx)
            scope_chain.append((obj_start, obj_end))
            if obj_start == 0 and obj_end == len(tokens):
                break
            if obj_start > 0:
                cur_idx = obj_start - 1
            else:
                break

        for s_start, s_end in reversed(scope_chain):
            scoped_tokens = list(tokens[s_start:s_end])
            scope_coll = ytl.YulParser(
                scoped_tokens,
                token_offset=s_start,
                protected_token_idxs=protected_token_idxs,
            ).collect_all_functions()
            scope_coll = ytl._exclude_collected_helpers_by_token_idx(
                scope_coll,
                authoritative_token_idxs,
            )
            ytl._merge_helper_collection(helper_table, rejected_helpers, scope_coll)

        body_range = ytl._find_function_body_range(list(tokens), fn_token_idx)
        if body_range is not None:
            body_start, body_end = body_range
            body_tokens = list(tokens[body_start:body_end])
            nested_coll = ytl.YulParser(
                body_tokens,
                token_offset=body_start,
                protected_token_idxs=protected_token_idxs,
            ).collect_all_functions()
            nested_coll = ytl._exclude_collected_helpers_by_token_idx(
                nested_coll,
                authoritative_token_idxs,
            )
            ytl._merge_helper_collection(helper_table, rejected_helpers, nested_coll)

        by_name: dict[str, str] = {raw_name: sol_name}
        for helper_name in list(helper_table):
            helper_fn = helper_table[helper_name]
            if (
                helper_fn.token_idx is not None
                and helper_fn.token_idx in all_selected_token_idxs
            ):
                by_name[helper_name] = token_idx_to_sol_name[helper_fn.token_idx]
                del helper_table[helper_name]
        target_call_resolutions[sol_name] = ytl.CallResolution(
            by_name=by_name,
            by_binding_token_idx=dict(token_idx_to_sol_name),
        )

        group_idx, top_level_func = _top_level_for_token(parsed_groups, fn_token_idx)
        helper_keys: list[FunctionKey] = []
        for helper_fn in helper_table.values():
            if helper_fn.token_idx is None:
                continue
            helper_keys.append(
                FunctionKey(
                    group_idx=_group_for_token(parsed_groups, helper_fn.token_idx),
                    token_idx=helper_fn.token_idx,
                )
            )

        target_infos[sol_name] = SelectedTargetInfo(
            sol_name=sol_name,
            key=FunctionKey(group_idx=group_idx, token_idx=fn_token_idx),
            raw_name=raw_name,
            lexical_path=lexical_path,
            top_level_key=FunctionKey(
                group_idx=group_idx,
                token_idx=top_level_func.span.start,
            ),
            helper_keys=tuple(helper_keys),
        )
        helper_tables[sol_name] = helper_table
        rejected_helper_tables[sol_name] = rejected_helpers

    return SelectionPlan(
        tokens=tokens,
        parsed_groups=parsed_groups,
        selected_functions=tuple(selected),
        helper_tables=helper_tables,
        rejected_helper_tables=rejected_helper_tables,
        target_call_resolutions=target_call_resolutions,
        target_infos=target_infos,
    )
