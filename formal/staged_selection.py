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

from yul_ast import (
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
    SynExpr,
    SynStmt,
    TopLevelFunctionTarget,
)
from yul_parser import SyntaxParser
from yul_resolve import ResolutionResult, resolve_module


def _span_size(item: tuple[int, FunctionDef]) -> int:
    """Sort key: span width of the FunctionDef in a (group_idx, func) pair."""
    return item[1].span.end - item[1].span.start


if TYPE_CHECKING:
    from yul_to_lean import ModelConfig


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

    parsed_groups: tuple[tuple[FunctionDef, ...], ...]
    selected_functions: tuple[str, ...]
    target_infos: dict[str, SelectedTargetInfo]


@dataclass(frozen=True)
class _SyntaxFunctionInfo:
    func: FunctionDef
    group_idx: int
    lexical_path: tuple[str, ...]
    top_level_token_idx: int
    top_level_name: str


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


def _direct_call_targets(
    func: FunctionDef,
    resolution: ResolutionResult,
) -> list[LocalFunctionTarget | TopLevelFunctionTarget | BuiltinTarget]:
    """Collect direct call targets from one function body.

    Nested function definitions are skipped: their dependencies are tracked
    when those helpers are visited recursively.
    """

    def walk_expr(expr: SynExpr, out: list[LocalFunctionTarget | TopLevelFunctionTarget | BuiltinTarget]) -> None:
        if isinstance(expr, CallExpr):
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
        if isinstance(stmt, LetStmt):
            if stmt.init is not None:
                walk_expr(stmt.init, out)
            return
        if isinstance(stmt, AssignStmt):
            walk_expr(stmt.expr, out)
            return
        if isinstance(stmt, ExprStmt):
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
        if isinstance(stmt, (FunctionDefStmt, LeaveStmt)):
            return

    def walk_block(
        block: Block,
        out: list[LocalFunctionTarget | TopLevelFunctionTarget | BuiltinTarget],
    ) -> None:
        for stmt in block.stmts:
            walk_stmt(stmt, out)

    out: list[LocalFunctionTarget | TopLevelFunctionTarget | BuiltinTarget] = []
    walk_block(func.body, out)
    return out


def _collect_helper_keys_for_target(
    *,
    target_info: _SyntaxFunctionInfo,
    resolved_group: dict[str, ResolutionResult],
    syntax_index: dict[int, _SyntaxFunctionInfo],
    selected_token_idxs: set[int],
) -> tuple[FunctionKey, ...]:
    by_name_span = {info.func.name_span: info for info in syntax_index.values()}
    top_level_by_name = {
        info.func.name: info
        for info in syntax_index.values()
        if info.func.span.start == info.top_level_token_idx
    }

    ordered: list[FunctionKey] = []
    seen: set[FunctionKey] = set()

    def resolve_helper_info(
        current_info: _SyntaxFunctionInfo,
        target: LocalFunctionTarget | TopLevelFunctionTarget | BuiltinTarget,
    ) -> _SyntaxFunctionInfo | None:
        if isinstance(target, BuiltinTarget):
            return None
        if isinstance(target, LocalFunctionTarget):
            outer_result = resolved_group[current_info.top_level_name]
            decl_info = outer_result.symbols.get(target.id)
            if decl_info is None:
                raise ParseError(
                    f"Resolver/local-helper index mismatch for {target.name!r}"
                )
            helper_info = by_name_span.get(decl_info.span)
            if helper_info is None:
                raise ParseError(
                    f"Missing syntax info for local helper {target.name!r}"
                )
            return helper_info
        helper_info = top_level_by_name.get(target.name)
        if helper_info is None:
            raise ParseError(
                f"Missing syntax info for top-level helper {target.name!r}"
            )
        return helper_info

    def visit(info: _SyntaxFunctionInfo) -> None:
        resolution = resolved_group[info.top_level_name]
        for target in _direct_call_targets(info.func, resolution):
            helper_info = resolve_helper_info(info, target)
            if helper_info is None:
                continue
            key = FunctionKey(
                group_idx=helper_info.group_idx,
                token_idx=helper_info.func.span.start,
            )
            if key.token_idx in selected_token_idxs or key in seen:
                continue
            seen.add(key)
            ordered.append(key)
            visit(helper_info)

    visit(target_info)
    return tuple(ordered)


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
    resolved_groups = tuple(
        resolve_module(list(func_group), builtins=ytl._EVM_BUILTINS)
        for func_group in parsed_groups
    )
    syntax_indexes = tuple(
        _index_group_functions(group_idx, funcs)
        for group_idx, funcs in enumerate(parsed_groups)
    )
    syntax_info_by_token_idx = {
        token_idx: info
        for syntax_index in syntax_indexes
        for token_idx, info in syntax_index.items()
    }

    selected = (
        selected_functions if selected_functions is not None else config.function_order
    )

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

    all_selected_token_idxs: set[int] = set()
    for sol_name in selected:
        token_idx = resolved_positions[sol_name][0]
        all_selected_token_idxs.add(token_idx)

    target_infos: dict[str, SelectedTargetInfo] = {}

    for sol_name in selected:
        fn_token_idx, raw_name, lexical_path = resolved_positions[sol_name]
        target_syntax = syntax_info_by_token_idx[fn_token_idx]
        group_idx = target_syntax.group_idx
        helper_keys = _collect_helper_keys_for_target(
            target_info=target_syntax,
            resolved_group=resolved_groups[group_idx],
            syntax_index=syntax_indexes[group_idx],
            selected_token_idxs=all_selected_token_idxs,
        )

        target_infos[sol_name] = SelectedTargetInfo(
            sol_name=sol_name,
            key=FunctionKey(group_idx=group_idx, token_idx=fn_token_idx),
            raw_name=raw_name,
            lexical_path=lexical_path,
            top_level_key=FunctionKey(
                group_idx=group_idx,
                token_idx=target_syntax.top_level_token_idx,
            ),
            helper_keys=helper_keys,
        )
    return SelectionPlan(
        parsed_groups=parsed_groups,
        selected_functions=tuple(selected),
        target_infos=target_infos,
    )
