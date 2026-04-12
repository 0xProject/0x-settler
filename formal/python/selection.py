"""
Select explicit Yul targets and collect the helpers visible from each target.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass, field
from typing import assert_never

from .evm_builtins import EVM_BUILTINS
from .model_config import FrozenMap, SelectionConfig
from .yul_ast import (
    AssignStmt,
    Block,
    BlockStmt,
    BuiltinTarget,
    CallExpr,
    ExprStmt,
    ForStmt,
    FunctionDef,
    FunctionDefStmt,
    IfStmt,
    LeaveStmt,
    LetStmt,
    LocalFunctionTarget,
    ParseError,
    SwitchStmt,
    SymbolId,
    SynExpr,
    SynStmt,
    TopLevelFunctionTarget,
)
from .yul_lexer import tokenize_yul
from .yul_parser import SyntaxParser
from .yul_resolve import ResolutionResult, resolve_module


@dataclass(frozen=True)
class FunctionKey:
    group_idx: int
    token_idx: int


@dataclass(frozen=True)
class SelectedFunctionInfo:
    key: FunctionKey
    raw_name: str
    lexical_path: tuple[str, ...]
    func: FunctionDef
    resolution: ResolutionResult
    top_level_name: str
    top_level_key: FunctionKey


@dataclass(frozen=True)
class SelectedTargetInfo:
    sol_name: str
    key: FunctionKey
    raw_name: str
    lexical_path: tuple[str, ...]
    func: FunctionDef
    resolution: ResolutionResult
    top_level_name: str
    top_level_key: FunctionKey
    helper_infos: tuple[SelectedFunctionInfo, ...]


@dataclass(frozen=True)
class SelectionPlan:
    selected_functions: tuple[str, ...]
    targets: Mapping[str, SelectedTargetInfo]

    def __post_init__(self) -> None:
        frozen_targets: FrozenMap[str, SelectedTargetInfo] = FrozenMap(self.targets)
        object.__setattr__(self, "targets", frozen_targets)


@dataclass(slots=True, frozen=True)
class _SyntaxFunctionInfo:
    func: FunctionDef
    group_idx: int
    lexical_path: tuple[str, ...]
    top_level_token_idx: int
    top_level_name: str

    @property
    def key(self) -> FunctionKey:
        return FunctionKey(self.group_idx, self.func.span.start)

    @property
    def top_level_key(self) -> FunctionKey:
        return FunctionKey(self.group_idx, self.top_level_token_idx)


@dataclass(slots=True)
class _SelectionIndex:
    resolved_groups: tuple[dict[str, ResolutionResult], ...]
    infos_in_token_order: tuple[_SyntaxFunctionInfo, ...]
    top_level_by_group_name: tuple[dict[str, _SyntaxFunctionInfo], ...]
    local_info_by_group_top_level: tuple[
        dict[str, dict[SymbolId, _SyntaxFunctionInfo]],
        ...,
    ]
    reachable_helper_keys: dict[FunctionKey, frozenset[FunctionKey]] = field(
        default_factory=dict
    )

    def wrapper_matches(
        self,
        sol_name: str,
        *,
        n_params: int | None = None,
    ) -> list[_SyntaxFunctionInfo]:
        target_prefix = f"fun_{sol_name}_"
        matches = [
            info
            for info in self.infos_in_token_order
            if len(info.lexical_path) == 1
            and info.func.name.startswith(target_prefix)
            and info.func.name[len(target_prefix) :].isdigit()
        ]
        if n_params is not None:
            matches = [info for info in matches if len(info.func.params) == n_params]
        return matches

    def exact_matches(
        self,
        yul_name: str,
        *,
        n_params: int | None = None,
        search_nested: bool,
    ) -> list[_SyntaxFunctionInfo]:
        return [
            info
            for info in self.infos_in_token_order
            if info.func.name == yul_name
            and (search_nested or len(info.lexical_path) == 1)
            and (n_params is None or len(info.func.params) == n_params)
        ]


def _normalize_requested_functions(
    config: SelectionConfig,
    requested: tuple[str, ...] | list[str] | None = None,
) -> tuple[str, ...]:
    selected = tuple(requested) if requested else config.function_order

    seen: set[str] = set()
    dupes: list[str] = []
    for name in selected:
        if name in seen and name not in dupes:
            dupes.append(name)
        seen.add(name)
    if dupes:
        raise ParseError(f"Duplicate selected functions: {sorted(dupes)}")

    allowed = set(config.function_order)
    bad = [name for name in selected if name not in allowed]
    if bad:
        raise ParseError(f"Unsupported function(s): {', '.join(bad)}")

    normalized = list(selected)
    if (
        any(name != config.inner_fn for name in normalized)
        and config.inner_fn not in normalized
    ):
        if config.inner_fn not in allowed:
            raise ParseError(
                f"Inner function {config.inner_fn!r} is not in function_order. "
                f"Available: {', '.join(config.function_order)}"
            )
        normalized.append(config.inner_fn)

    normalized_set = set(normalized)
    return tuple(name for name in config.function_order if name in normalized_set)


def build_selection_plan(
    yul_text: str,
    config: SelectionConfig,
    *,
    selected_functions: tuple[str, ...] | None = None,
) -> SelectionPlan:
    tokens = tuple(tokenize_yul(yul_text))
    index = _build_selection_index(list(tokens))

    selected = _normalize_requested_functions(config, selected_functions)
    candidate_lists = _build_candidate_lists(index, config, selected)
    resolved_infos = _resolve_candidates(index, config, selected, candidate_lists)
    selected_keys = {info.key for info in resolved_infos.values()}

    targets: dict[str, SelectedTargetInfo] = {}
    for sol_name in selected:
        info = resolved_infos[sol_name]
        helper_infos = _collect_helper_infos_for_target(
            index=index,
            target_info=info,
            exclude_keys=selected_keys,
        )
        targets[sol_name] = SelectedTargetInfo(
            sol_name=sol_name,
            key=info.key,
            raw_name=info.func.name,
            lexical_path=info.lexical_path,
            func=info.func,
            resolution=index.resolved_groups[info.group_idx][info.top_level_name],
            top_level_name=info.top_level_name,
            top_level_key=info.top_level_key,
            helper_infos=helper_infos,
        )
    return SelectionPlan(
        selected_functions=selected,
        targets=targets,
    )


def _build_candidate_lists(
    index: _SelectionIndex,
    config: SelectionConfig,
    selected: tuple[str, ...],
) -> dict[str, list[_SyntaxFunctionInfo]]:
    candidates: dict[str, list[_SyntaxFunctionInfo]] = {}
    for sol_name in selected:
        n_params = config.n_params.get(sol_name)
        exact_selector = config.exact_yul_names.get(sol_name)
        if exact_selector is not None:
            candidates[sol_name] = _select_exact_matches(
                index=index,
                selector=exact_selector,
                n_params=n_params,
            )
            continue

        matches = index.wrapper_matches(sol_name, n_params=n_params)
        if not matches:
            if n_params is None:
                raise ParseError(
                    f"Yul function for '{sol_name}' not found "
                    f"(expected pattern fun_{sol_name}_<digits>)"
                )
            raise ParseError(
                f"No Yul function for {sol_name!r} matches {n_params} parameter(s)"
            )
        candidates[sol_name] = matches
    return candidates


def _resolve_candidates(
    index: _SelectionIndex,
    config: SelectionConfig,
    selected: tuple[str, ...],
    candidate_lists: dict[str, list[_SyntaxFunctionInfo]],
) -> dict[str, _SyntaxFunctionInfo]:
    for sol_name, avoid_names in config.avoid_reaching_selected.items():
        if sol_name not in candidate_lists:
            raise ParseError(
                f"avoid_reaching_selected references unknown function {sol_name!r}"
            )
        unknown = sorted(name for name in avoid_names if name not in candidate_lists)
        if unknown:
            raise ParseError(
                f"avoid_reaching_selected[{sol_name!r}] references unknown "
                f"selected function(s): {', '.join(unknown)}"
            )
    for sol_name, require_names in config.require_reaching_selected.items():
        if sol_name not in candidate_lists:
            raise ParseError(
                f"require_reaching_selected references unknown function {sol_name!r}"
            )
        unknown = sorted(name for name in require_names if name not in candidate_lists)
        if unknown:
            raise ParseError(
                f"require_reaching_selected[{sol_name!r}] references unknown "
                f"selected function(s): {', '.join(unknown)}"
            )

    current = {name: list(matches) for name, matches in candidate_lists.items()}
    resolved = {
        name: matches[0] for name, matches in current.items() if len(matches) == 1
    }

    changed = True
    while changed:
        changed = False
        for sol_name in selected:
            if sol_name in resolved:
                continue
            matches = current[sol_name]
            filtered = _apply_require_reaching_filter(
                index=index,
                sol_name=sol_name,
                matches=matches,
                resolved=resolved,
                require_names=config.require_reaching_selected.get(
                    sol_name, frozenset()
                ),
            )
            if len(filtered) != len(matches):
                current[sol_name] = filtered
                matches = filtered
                changed = True
            filtered = _apply_avoid_reaching_filter(
                index=index,
                sol_name=sol_name,
                matches=matches,
                resolved=resolved,
                avoid_names=config.avoid_reaching_selected.get(sol_name, frozenset()),
            )
            if len(filtered) != len(matches):
                current[sol_name] = filtered
                matches = filtered
                changed = True
            if len(matches) == 1:
                resolved[sol_name] = matches[0]
                changed = True

    unresolved = {
        name: matches for name, matches in current.items() if len(matches) > 1
    }
    if unresolved:
        sol_name = next(name for name in selected if name in unresolved)
        names = [info.func.name for info in unresolved[sol_name]]
        raise ParseError(
            f"Multiple Yul functions match '{sol_name}': {names}. "
            f"Pass exact_yul_names or avoid_reaching_selected to disambiguate."
        )
    return resolved


def _apply_require_reaching_filter(
    *,
    index: _SelectionIndex,
    sol_name: str,
    matches: list[_SyntaxFunctionInfo],
    resolved: dict[str, _SyntaxFunctionInfo],
    require_names: frozenset[str],
) -> list[_SyntaxFunctionInfo]:
    if not require_names:
        return matches
    if any(name not in resolved for name in require_names):
        return matches

    required = {resolved[name].key for name in require_names}
    filtered = [
        info
        for info in matches
        if required.issubset(_collect_reachable_helper_keys(index, info))
    ]
    if not filtered:
        raise ParseError(
            f"No Yul function for {sol_name!r} reaches selected helper "
            f"dependencies {sorted(require_names)!r}"
        )
    return filtered


def _apply_avoid_reaching_filter(
    *,
    index: _SelectionIndex,
    sol_name: str,
    matches: list[_SyntaxFunctionInfo],
    resolved: dict[str, _SyntaxFunctionInfo],
    avoid_names: frozenset[str],
) -> list[_SyntaxFunctionInfo]:
    if not avoid_names:
        return matches
    if any(name not in resolved for name in avoid_names):
        return matches

    forbidden = {resolved[name].key for name in avoid_names}
    filtered = [
        info
        for info in matches
        if forbidden.isdisjoint(_collect_reachable_helper_keys(index, info))
    ]
    if not filtered:
        raise ParseError(
            f"No Yul function for {sol_name!r} avoids selected helper reachability "
            f"to {sorted(avoid_names)!r}"
        )
    return filtered


def _select_exact_matches(
    *,
    index: _SelectionIndex,
    selector: str,
    n_params: int | None,
) -> list[_SyntaxFunctionInfo]:
    exact_path = _parse_exact_yul_selector(selector)
    if exact_path is None:
        matches = index.exact_matches(
            selector,
            n_params=n_params,
            search_nested=True,
        )
    else:
        matches = [
            info
            for info in index.exact_matches(
                exact_path[-1],
                n_params=n_params,
                search_nested=True,
            )
            if info.lexical_path == exact_path
        ]

    if not matches:
        if n_params is not None:
            if exact_path is None:
                raise ParseError(
                    f"Exact Yul function {selector!r} with "
                    f"{n_params} parameter(s) not found"
                )
            raise ParseError(
                f"Exact Yul function path {'::'.join(exact_path)!r} with "
                f"{n_params} parameter(s) not found"
            )
        if exact_path is None:
            raise ParseError(f"Exact Yul function {selector!r} not found")
        raise ParseError(f"Exact Yul function path {'::'.join(exact_path)!r} not found")

    if len(matches) > 1:
        rendered = "::".join(exact_path) if exact_path is not None else selector
        raise ParseError(
            f"Multiple exact Yul functions matched {rendered!r}. Refuse to guess."
        )
    return matches


def _parse_exact_yul_selector(selector: str) -> tuple[str, ...] | None:
    if "::" not in selector:
        return None
    raw = selector[2:] if selector.startswith("::") else selector
    parts = tuple(raw.split("::"))
    if any(not part for part in parts):
        raise ParseError(f"Invalid exact Yul selector {selector!r}")
    return parts


def _build_selection_index(
    tokens: list[tuple[str, str]],
) -> _SelectionIndex:
    parsed_groups = tuple(
        tuple(group) for group in SyntaxParser(list(tokens)).parse_function_groups()
    )
    resolved_groups = tuple(
        resolve_module(list(func_group), builtins=EVM_BUILTINS)
        for func_group in parsed_groups
    )
    syntax_indexes = tuple(
        _index_group_functions(group_idx, funcs)
        for group_idx, funcs in enumerate(parsed_groups)
    )
    infos_in_token_order = tuple(
        sorted(
            (info for syntax_index in syntax_indexes for info in syntax_index.values()),
            key=_syntax_info_token_start,
        )
    )
    top_level_by_group_name = tuple(
        {
            info.func.name: info
            for info in syntax_index.values()
            if info.func.span.start == info.top_level_token_idx
        }
        for syntax_index in syntax_indexes
    )
    local_info_by_group_top_level: list[
        dict[str, dict[SymbolId, _SyntaxFunctionInfo]]
    ] = []
    for group_idx, resolved_group in enumerate(resolved_groups):
        syntax_index = syntax_indexes[group_idx]
        by_name_span = {info.func.name_span: info for info in syntax_index.values()}
        per_top_level: dict[str, dict[SymbolId, _SyntaxFunctionInfo]] = {}
        for top_level_name, result in resolved_group.items():
            per_top_level[top_level_name] = {
                sid: by_name_span[decl_info.span]
                for sid, decl_info in result.symbols.items()
                if decl_info.span in by_name_span
            }
        local_info_by_group_top_level.append(per_top_level)
    return _SelectionIndex(
        resolved_groups=resolved_groups,
        infos_in_token_order=infos_in_token_order,
        top_level_by_group_name=top_level_by_group_name,
        local_info_by_group_top_level=tuple(local_info_by_group_top_level),
    )


def _syntax_info_token_start(info: _SyntaxFunctionInfo) -> int:
    return info.func.span.start


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


def _collect_helper_infos_for_target(
    *,
    index: _SelectionIndex,
    target_info: _SyntaxFunctionInfo,
    exclude_keys: set[FunctionKey],
) -> tuple[SelectedFunctionInfo, ...]:
    ordered: list[_SyntaxFunctionInfo] = []
    seen: set[FunctionKey] = set()

    def visit(info: _SyntaxFunctionInfo) -> None:
        for helper_info in _direct_helper_infos(index, info):
            if helper_info.key in exclude_keys or helper_info.key in seen:
                continue
            seen.add(helper_info.key)
            ordered.append(helper_info)
            visit(helper_info)

    visit(target_info)
    return tuple(
        SelectedFunctionInfo(
            key=helper.key,
            raw_name=helper.func.name,
            lexical_path=helper.lexical_path,
            func=helper.func,
            resolution=index.resolved_groups[helper.group_idx][helper.top_level_name],
            top_level_name=helper.top_level_name,
            top_level_key=helper.top_level_key,
        )
        for helper in ordered
    )


def _collect_reachable_helper_keys(
    index: _SelectionIndex,
    target_info: _SyntaxFunctionInfo,
) -> frozenset[FunctionKey]:
    cached = index.reachable_helper_keys.get(target_info.key)
    if cached is not None:
        return cached
    cached = frozenset(
        helper.key
        for helper in _collect_helper_infos_for_target(
            index=index,
            target_info=target_info,
            exclude_keys=set(),
        )
    )
    index.reachable_helper_keys[target_info.key] = cached
    return cached


def _direct_helper_infos(
    index: _SelectionIndex,
    info: _SyntaxFunctionInfo,
) -> list[_SyntaxFunctionInfo]:
    resolved_group = index.resolved_groups[info.group_idx]
    resolution = resolved_group[info.top_level_name]
    direct_targets = _direct_call_targets(info.func, resolution)
    out: list[_SyntaxFunctionInfo] = []
    for target in direct_targets:
        helper_info = _resolve_helper_info(index, info, target)
        if helper_info is not None:
            out.append(helper_info)
    return out


def _resolve_helper_info(
    index: _SelectionIndex,
    current_info: _SyntaxFunctionInfo,
    target: LocalFunctionTarget | TopLevelFunctionTarget | BuiltinTarget,
) -> _SyntaxFunctionInfo | None:
    if isinstance(target, BuiltinTarget):
        return None
    if isinstance(target, LocalFunctionTarget):
        outer_result = index.resolved_groups[current_info.group_idx][
            current_info.top_level_name
        ]
        decl_info = outer_result.symbols.get(target.id)
        if decl_info is None:
            raise ParseError(
                f"Resolver/local-helper index mismatch for {target.name!r}"
            )
        helper_info = index.local_info_by_group_top_level[current_info.group_idx][
            current_info.top_level_name
        ].get(target.id)
        if helper_info is None:
            raise ParseError(f"Missing syntax info for local helper {target.name!r}")
        return helper_info
    helper_info = index.top_level_by_group_name[current_info.group_idx].get(target.name)
    if helper_info is None:
        raise ParseError(f"Missing syntax info for top-level helper {target.name!r}")
    return helper_info


def _direct_call_targets(
    func: FunctionDef,
    resolution: ResolutionResult,
) -> list[LocalFunctionTarget | TopLevelFunctionTarget | BuiltinTarget]:
    def walk_expr(
        expr: SynExpr,
        out: list[LocalFunctionTarget | TopLevelFunctionTarget | BuiltinTarget],
    ) -> None:
        if not isinstance(expr, CallExpr):
            return
        target = resolution.call_targets.get(expr.name_span)
        if target is None:
            raise ParseError(
                f"Resolver omitted call target for {expr.name!r} "
                f"at span {expr.name_span!r}"
            )
        if isinstance(
            target,
            (BuiltinTarget, LocalFunctionTarget, TopLevelFunctionTarget),
        ):
            out.append(target)
        for arg in expr.args:
            walk_expr(arg, out)

    def walk_stmt(
        stmt: SynStmt,
        out: list[LocalFunctionTarget | TopLevelFunctionTarget | BuiltinTarget],
    ) -> None:
        if isinstance(stmt, FunctionDefStmt):
            return
        if isinstance(stmt, ExprStmt):
            walk_expr(stmt.expr, out)
            return
        if isinstance(stmt, AssignStmt):
            walk_expr(stmt.expr, out)
            return
        if isinstance(stmt, BlockStmt):
            walk_block(stmt.block, out)
            return
        if isinstance(stmt, IfStmt):
            walk_expr(stmt.condition, out)
            walk_block(stmt.body, out)
            return
        if isinstance(stmt, SwitchStmt):
            walk_expr(stmt.discriminant, out)
            for case in stmt.cases:
                walk_expr(case.value, out)
                walk_block(case.body, out)
            if stmt.default is not None:
                walk_block(stmt.default.body, out)
            return
        if isinstance(stmt, ForStmt):
            walk_block(stmt.init, out)
            walk_expr(stmt.condition, out)
            walk_block(stmt.post, out)
            walk_block(stmt.body, out)
            return
        if isinstance(stmt, LeaveStmt):
            return
        if isinstance(stmt, LetStmt):
            if stmt.init is not None:
                walk_expr(stmt.init, out)
            return
        assert_never(stmt)

    def walk_block(
        block: Block,
        out: list[LocalFunctionTarget | TopLevelFunctionTarget | BuiltinTarget],
    ) -> None:
        for stmt in block.stmts:
            walk_stmt(stmt, out)

    out: list[LocalFunctionTarget | TopLevelFunctionTarget | BuiltinTarget] = []
    walk_block(func.body, out)
    return out
