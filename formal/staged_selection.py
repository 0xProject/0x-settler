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
from typing import TYPE_CHECKING, assert_never

from evm_builtins import EVM_BUILTINS, WORD_MOD, try_eval_pure_builtin
from yul_lexer import tokenize_yul
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
    IntExpr,
    LeaveStmt,
    LetStmt,
    LocalFunctionTarget,
    NameExpr,
    ParseError,
    StringExpr,
    SymbolId,
    SwitchStmt,
    SynExpr,
    SynStmt,
    TopLevelFunctionTarget,
    UnresolvedTarget,
)
from yul_parser import SyntaxParser
from yul_resolve import ResolutionResult, resolve_module

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
    resolved_groups: tuple[dict[str, ResolutionResult], ...]
    syntax_indexes: tuple[dict[int, _SyntaxFunctionInfo], ...]
    selected_functions: tuple[str, ...]
    target_infos: dict[str, SelectedTargetInfo]


@dataclass(frozen=True)
class _SyntaxFunctionInfo:
    func: FunctionDef
    group_idx: int
    lexical_path: tuple[str, ...]
    top_level_token_idx: int
    top_level_name: str


@dataclass(frozen=True)
class _KnownFunctionCriteria:
    keys: frozenset[FunctionKey] = frozenset()
    names: frozenset[str] = frozenset()


@dataclass(frozen=True)
class _ReferenceAnalysisResult:
    live_references: bool
    dead_references: bool
    definitely_terminates: bool


@dataclass(frozen=True)
class _SelectionIndex:
    parsed_groups: tuple[tuple[FunctionDef, ...], ...]
    resolved_groups: tuple[dict[str, ResolutionResult], ...]
    syntax_indexes: tuple[dict[int, _SyntaxFunctionInfo], ...]
    infos_in_token_order: tuple[_SyntaxFunctionInfo, ...]
    top_level_by_group_name: tuple[dict[str, _SyntaxFunctionInfo], ...]
    local_info_by_group_top_level: tuple[
        dict[str, dict[SymbolId, _SyntaxFunctionInfo]],
        ...,
    ]

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

    def disambiguate_by_references(
        self,
        matches: list[_SyntaxFunctionInfo],
        *,
        known: _KnownFunctionCriteria,
        exclude_known: bool,
    ) -> list[_SyntaxFunctionInfo]:
        summaries = {
            _function_key(info): self._body_reference_summary(info, known)
            for info in matches
        }

        def _summary(info: _SyntaxFunctionInfo) -> _ReferenceAnalysisResult:
            return summaries[_function_key(info)]

        if exclude_known:
            live_independent = [
                info for info in matches if not _summary(info).live_references
            ]
            if live_independent:
                dead_tiebreak = [
                    info for info in live_independent if _summary(info).dead_references
                ]
                return dead_tiebreak if dead_tiebreak else live_independent
            return matches

        live_dependent = [info for info in matches if _summary(info).live_references]
        if live_dependent:
            return live_dependent
        clean_candidates = [info for info in matches if not _summary(info).dead_references]
        if clean_candidates:
            return clean_candidates
        return matches

    def _body_reference_summary(
        self,
        info: _SyntaxFunctionInfo,
        known: _KnownFunctionCriteria,
    ) -> _ReferenceAnalysisResult:
        result = self.resolved_groups[info.group_idx][info.top_level_name]
        return self._scope_reference_summary(
            info.func.body,
            result=result,
            group_idx=info.group_idx,
            top_level_name=info.top_level_name,
            known=known,
            visible_local_summaries={},
        )

    def _scope_reference_summary(
        self,
        block: Block,
        *,
        result: ResolutionResult,
        group_idx: int,
        top_level_name: str,
        known: _KnownFunctionCriteria,
        visible_local_summaries: dict[SymbolId, _ReferenceAnalysisResult],
    ) -> _ReferenceAnalysisResult:
        local_functions = [
            stmt.func for stmt in block.stmts if isinstance(stmt, FunctionDefStmt)
        ]
        local_summaries: dict[SymbolId, _ReferenceAnalysisResult] = {
            result.declarations[func.name_span]: _ReferenceAnalysisResult(
                live_references=False,
                dead_references=False,
                definitely_terminates=False,
            )
            for func in local_functions
        }

        changed = True
        while changed:
            changed = False
            combined = {**visible_local_summaries, **local_summaries}
            for func in local_functions:
                sid = result.declarations[func.name_span]
                summary = self._scope_reference_summary(
                    func.body,
                    result=result,
                    group_idx=group_idx,
                    top_level_name=top_level_name,
                    known=known,
                    visible_local_summaries=combined,
                )
                if summary != local_summaries[sid]:
                    local_summaries[sid] = summary
                    changed = True

        combined = {**visible_local_summaries, **local_summaries}
        live = False
        dead = False
        terminated = False
        for stmt in block.stmts:
            if isinstance(stmt, FunctionDefStmt):
                continue
            stmt_summary = self._statement_reference_summary(
                stmt,
                result=result,
                group_idx=group_idx,
                top_level_name=top_level_name,
                known=known,
                visible_local_summaries=combined,
            )
            if terminated:
                dead = dead or stmt_summary.live_references or stmt_summary.dead_references
                continue
            live = live or stmt_summary.live_references
            dead = dead or stmt_summary.dead_references
            terminated = stmt_summary.definitely_terminates
        return _ReferenceAnalysisResult(live, dead, terminated)

    def _statement_reference_summary(
        self,
        stmt: SynStmt,
        *,
        result: ResolutionResult,
        group_idx: int,
        top_level_name: str,
        known: _KnownFunctionCriteria,
        visible_local_summaries: dict[SymbolId, _ReferenceAnalysisResult],
    ) -> _ReferenceAnalysisResult:
        if isinstance(stmt, LetStmt):
            if stmt.init is None:
                return _ReferenceAnalysisResult(False, False, False)
            return self._expr_reference_summary(
                stmt.init,
                result=result,
                group_idx=group_idx,
                top_level_name=top_level_name,
                known=known,
                visible_local_summaries=visible_local_summaries,
            )

        if isinstance(stmt, (AssignStmt, ExprStmt)):
            return self._expr_reference_summary(
                stmt.expr,
                result=result,
                group_idx=group_idx,
                top_level_name=top_level_name,
                known=known,
                visible_local_summaries=visible_local_summaries,
            )

        if isinstance(stmt, LeaveStmt):
            return _ReferenceAnalysisResult(False, False, True)

        if isinstance(stmt, BlockStmt):
            return self._scope_reference_summary(
                stmt.block,
                result=result,
                group_idx=group_idx,
                top_level_name=top_level_name,
                known=known,
                visible_local_summaries=visible_local_summaries,
            )

        if isinstance(stmt, IfStmt):
            cond_summary = self._expr_reference_summary(
                stmt.condition,
                result=result,
                group_idx=group_idx,
                top_level_name=top_level_name,
                known=known,
                visible_local_summaries=visible_local_summaries,
            )
            const_cond = _try_const_eval_syn(stmt.condition)
            if const_cond is not None:
                live = cond_summary.live_references
                dead = cond_summary.dead_references
                then_summary = self._scope_reference_summary(
                    stmt.body,
                    result=result,
                    group_idx=group_idx,
                    top_level_name=top_level_name,
                    known=known,
                    visible_local_summaries=visible_local_summaries,
                )
                if const_cond != 0:
                    return _ReferenceAnalysisResult(
                        live or then_summary.live_references,
                        dead or then_summary.dead_references,
                        then_summary.definitely_terminates,
                    )
                return _ReferenceAnalysisResult(
                    live,
                    dead or then_summary.live_references or then_summary.dead_references,
                    False,
                )

            then_summary = self._scope_reference_summary(
                stmt.body,
                result=result,
                group_idx=group_idx,
                top_level_name=top_level_name,
                known=known,
                visible_local_summaries=visible_local_summaries,
            )
            return _ReferenceAnalysisResult(
                cond_summary.live_references or then_summary.live_references,
                cond_summary.dead_references or then_summary.dead_references,
                False,
            )

        if isinstance(stmt, SwitchStmt):
            discrim_summary = self._expr_reference_summary(
                stmt.discriminant,
                result=result,
                group_idx=group_idx,
                top_level_name=top_level_name,
                known=known,
                visible_local_summaries=visible_local_summaries,
            )
            const_disc = _try_const_eval_syn(stmt.discriminant)
            if const_disc is not None:
                chosen_summary: _ReferenceAnalysisResult | None = None
                dead = discrim_summary.dead_references
                for case in stmt.cases:
                    case_val = _try_const_eval_syn(case.value)
                    case_summary = self._scope_reference_summary(
                        case.body,
                        result=result,
                        group_idx=group_idx,
                        top_level_name=top_level_name,
                        known=known,
                        visible_local_summaries=visible_local_summaries,
                    )
                    if case_val is not None and case_val == const_disc:
                        chosen_summary = case_summary
                    else:
                        dead = (
                            dead
                            or case_summary.live_references
                            or case_summary.dead_references
                        )
                default_summary = (
                    self._scope_reference_summary(
                        stmt.default.body,
                        result=result,
                        group_idx=group_idx,
                        top_level_name=top_level_name,
                        known=known,
                        visible_local_summaries=visible_local_summaries,
                    )
                    if stmt.default is not None
                    else None
                )
                if chosen_summary is None:
                    chosen_summary = default_summary
                elif default_summary is not None:
                    dead = (
                        dead
                        or default_summary.live_references
                        or default_summary.dead_references
                    )
                if chosen_summary is None:
                    return _ReferenceAnalysisResult(
                        discrim_summary.live_references,
                        dead,
                        False,
                    )
                return _ReferenceAnalysisResult(
                    discrim_summary.live_references or chosen_summary.live_references,
                    dead or chosen_summary.dead_references,
                    chosen_summary.definitely_terminates,
                )

            branch_summaries = [
                self._scope_reference_summary(
                    case.body,
                    result=result,
                    group_idx=group_idx,
                    top_level_name=top_level_name,
                    known=known,
                    visible_local_summaries=visible_local_summaries,
                )
                for case in stmt.cases
            ]
            default_summary = (
                self._scope_reference_summary(
                    stmt.default.body,
                    result=result,
                    group_idx=group_idx,
                    top_level_name=top_level_name,
                    known=known,
                    visible_local_summaries=visible_local_summaries,
                )
                if stmt.default is not None
                else None
            )
            return _ReferenceAnalysisResult(
                discrim_summary.live_references
                or any(summary.live_references for summary in branch_summaries)
                or (
                    default_summary.live_references
                    if default_summary is not None
                    else False
                ),
                discrim_summary.dead_references
                or any(summary.dead_references for summary in branch_summaries)
                or (
                    default_summary.dead_references
                    if default_summary is not None
                    else False
                ),
                default_summary is not None
                and all(summary.definitely_terminates for summary in branch_summaries)
                and default_summary.definitely_terminates,
            )

        if isinstance(stmt, ForStmt):
            init_summary = self._scope_reference_summary(
                stmt.init,
                result=result,
                group_idx=group_idx,
                top_level_name=top_level_name,
                known=known,
                visible_local_summaries=visible_local_summaries,
            )
            cond_summary = self._expr_reference_summary(
                stmt.condition,
                result=result,
                group_idx=group_idx,
                top_level_name=top_level_name,
                known=known,
                visible_local_summaries=visible_local_summaries,
            )
            body_summary = self._scope_reference_summary(
                stmt.body,
                result=result,
                group_idx=group_idx,
                top_level_name=top_level_name,
                known=known,
                visible_local_summaries=visible_local_summaries,
            )
            post_summary = self._scope_reference_summary(
                stmt.post,
                result=result,
                group_idx=group_idx,
                top_level_name=top_level_name,
                known=known,
                visible_local_summaries=visible_local_summaries,
            )

            if init_summary.definitely_terminates:
                return _ReferenceAnalysisResult(
                    init_summary.live_references,
                    init_summary.dead_references
                    or cond_summary.live_references
                    or cond_summary.dead_references
                    or body_summary.live_references
                    or body_summary.dead_references
                    or post_summary.live_references
                    or post_summary.dead_references,
                    True,
                )

            const_cond = _try_const_eval_syn(stmt.condition)
            if const_cond is not None and const_cond == 0:
                return _ReferenceAnalysisResult(
                    init_summary.live_references or cond_summary.live_references,
                    init_summary.dead_references
                    or cond_summary.dead_references
                    or body_summary.live_references
                    or body_summary.dead_references
                    or post_summary.live_references
                    or post_summary.dead_references,
                    False,
                )

            return _ReferenceAnalysisResult(
                init_summary.live_references
                or cond_summary.live_references
                or body_summary.live_references
                or post_summary.live_references,
                init_summary.dead_references
                or cond_summary.dead_references
                or body_summary.dead_references
                or post_summary.dead_references,
                const_cond is not None and const_cond != 0,
            )

        if isinstance(stmt, FunctionDefStmt):
            return _ReferenceAnalysisResult(False, False, False)

        assert_never(stmt)

    def _expr_reference_summary(
        self,
        expr: SynExpr,
        *,
        result: ResolutionResult,
        group_idx: int,
        top_level_name: str,
        known: _KnownFunctionCriteria,
        visible_local_summaries: dict[SymbolId, _ReferenceAnalysisResult],
    ) -> _ReferenceAnalysisResult:
        if isinstance(expr, (IntExpr, NameExpr, StringExpr)):
            return _ReferenceAnalysisResult(False, False, False)

        if not isinstance(expr, CallExpr):
            assert_never(expr)

        live = False
        dead = False
        target = result.call_targets.get(expr.name_span)
        if target is None:
            raise ParseError(
                f"Resolver omitted call target for {expr.name!r} "
                f"at span {expr.name_span!r}"
            )
        if isinstance(target, TopLevelFunctionTarget):
            helper_info = self.top_level_by_group_name[group_idx].get(target.name)
            if helper_info is None:
                raise ParseError(
                    f"Missing syntax info for top-level helper {target.name!r}"
                )
            if _known_matches_info(helper_info, known):
                live = True
        elif isinstance(target, LocalFunctionTarget):
            helper_info = self.local_info_by_group_top_level[group_idx][top_level_name].get(
                target.id
            )
            if helper_info is None:
                raise ParseError(
                    f"Missing syntax info for local helper {target.name!r}"
                )
            if _known_matches_info(helper_info, known):
                live = True
            summary = visible_local_summaries.get(target.id)
            if summary is None:
                raise ParseError(
                    f"Missing visible summary for local helper {target.name!r}"
                )
            live = live or summary.live_references
            dead = dead or summary.dead_references
        elif not isinstance(target, (BuiltinTarget, UnresolvedTarget)):
            assert_never(target)

        for arg in expr.args:
            child = self._expr_reference_summary(
                arg,
                result=result,
                group_idx=group_idx,
                top_level_name=top_level_name,
                known=known,
                visible_local_summaries=visible_local_summaries,
            )
            live = live or child.live_references
            dead = dead or child.dead_references
        return _ReferenceAnalysisResult(live, dead, False)


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


def _build_selection_index(
    tokens: list[tuple[str, str]],
    *,
    builtins: frozenset[str],
) -> _SelectionIndex:
    parsed_groups = tuple(
        tuple(g) for g in SyntaxParser(list(tokens)).parse_function_groups()
    )
    resolved_groups = tuple(
        resolve_module(list(func_group), builtins=builtins)
        for func_group in parsed_groups
    )
    syntax_indexes = tuple(
        _index_group_functions(group_idx, funcs)
        for group_idx, funcs in enumerate(parsed_groups)
    )
    infos_in_token_order = tuple(
        sorted(
            (
                info
                for syntax_index in syntax_indexes
                for info in syntax_index.values()
            ),
            key=lambda info: info.func.span.start,
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
    local_info_by_group_top_level: list[dict[str, dict[SymbolId, _SyntaxFunctionInfo]]] = []
    for group_idx, resolved_group in enumerate(resolved_groups):
        syntax_index = syntax_indexes[group_idx]
        by_name_span = {
            info.func.name_span: info
            for info in syntax_index.values()
        }
        per_top_level: dict[str, dict[SymbolId, _SyntaxFunctionInfo]] = {}
        for top_level_name, result in resolved_group.items():
            per_top_level[top_level_name] = {
                sid: by_name_span[decl_info.span]
                for sid, decl_info in result.symbols.items()
                if decl_info.span in by_name_span
            }
        local_info_by_group_top_level.append(per_top_level)
    return _SelectionIndex(
        parsed_groups=parsed_groups,
        resolved_groups=resolved_groups,
        syntax_indexes=syntax_indexes,
        infos_in_token_order=infos_in_token_order,
        top_level_by_group_name=top_level_by_group_name,
        local_info_by_group_top_level=tuple(local_info_by_group_top_level),
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


def _function_key(info: _SyntaxFunctionInfo) -> FunctionKey:
    return FunctionKey(group_idx=info.group_idx, token_idx=info.func.span.start)


def _known_matches_info(
    info: _SyntaxFunctionInfo,
    known: _KnownFunctionCriteria,
) -> bool:
    return _function_key(info) in known.keys or info.func.name in known.names


def _try_const_eval_syn(expr: SynExpr) -> int | None:
    if isinstance(expr, IntExpr):
        return expr.value % WORD_MOD
    if isinstance(expr, (NameExpr, StringExpr)):
        return None
    if not isinstance(expr, CallExpr):
        assert_never(expr)
    values: list[int] = []
    for arg in expr.args:
        value = _try_const_eval_syn(arg)
        if value is None:
            return None
        values.append(value)
    return try_eval_pure_builtin(expr.name, tuple(values))


def _parse_exact_yul_selector(selector: str) -> tuple[str, ...] | None:
    """Parse a scope-qualified exact Yul selector.

    ``None`` means the selector is an unqualified function name.
    ``::top`` selects a top-level function. ``outer::helper`` selects a
    function nested inside ``outer``.
    """
    if "::" not in selector:
        return None
    raw = selector[2:] if selector.startswith("::") else selector
    parts = tuple(raw.split("::"))
    if any(not part for part in parts):
        raise ParseError(f"Invalid exact Yul selector {selector!r}")
    return parts


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

    tokens = tuple(tokenize_yul(yul_text))
    index = _build_selection_index(list(tokens), builtins=EVM_BUILTINS)
    syntax_info_by_token_idx = {
        token_idx: info
        for syntax_index in index.syntax_indexes
        for token_idx, info in syntax_index.items()
    }

    selected = (
        selected_functions if selected_functions is not None else config.function_order
    )

    resolved_positions: dict[str, tuple[int, str, tuple[str, ...]]] = {}
    known_exact_keys: set[FunctionKey] = set()
    for sol_name in selected:
        if (
            config.exact_yul_names is not None
            and config.exact_yul_names.get(sol_name) is not None
        ):
            exact_yul_name = config.exact_yul_names[sol_name]
            exact_selector = _parse_exact_yul_selector(exact_yul_name)
            n_params = config.n_params.get(sol_name) if config.n_params else None
            if exact_selector is None:
                matches = index.exact_matches(
                    exact_yul_name,
                    n_params=n_params,
                    search_nested=True,
                )
            else:
                matches = [
                    info
                    for info in index.exact_matches(
                        exact_selector[-1],
                        n_params=n_params,
                        search_nested=True,
                    )
                    if info.lexical_path == exact_selector
                ]
            if not matches:
                if n_params is not None:
                    if exact_selector is None:
                        raise ParseError(
                            f"Exact Yul function {exact_yul_name!r} with "
                            f"{n_params} parameter(s) not found"
                        )
                    raise ParseError(
                        f"Exact Yul function path {'::'.join(exact_selector)!r} "
                        f"with {n_params} parameter(s) not found"
                    )
                if exact_selector is None:
                    raise ParseError(
                        f"Exact Yul function {exact_yul_name!r} not found"
                    )
                raise ParseError(
                    f"Exact Yul function path {'::'.join(exact_selector)!r} not found"
                )
            if len(matches) > 1:
                rendered = (
                    "::".join(exact_selector)
                    if exact_selector is not None
                    else exact_yul_name
                )
                raise ParseError(
                    f"Multiple exact Yul functions matched {rendered!r}. Refuse to guess."
                )
            match = matches[0]
            resolved_positions[sol_name] = (
                match.func.span.start,
                match.lexical_path[-1],
                match.lexical_path,
            )
        else:
            n_params = config.n_params.get(sol_name) if config.n_params else None
            all_matches = index.wrapper_matches(sol_name)
            if not all_matches:
                raise ParseError(
                    f"Yul function for '{sol_name}' not found "
                    f"(expected pattern fun_{sol_name}_<digits>)"
                )
            matches = (
                [info for info in all_matches if len(info.func.params) == n_params]
                if n_params is not None
                else all_matches
            )
            if n_params is not None and not matches:
                raise ParseError(
                    f"No Yul function for {sol_name!r} matches "
                    f"{n_params} parameter(s)"
                )
            if known_exact_keys and len(matches) > 1:
                matches = index.disambiguate_by_references(
                    matches,
                    known=_KnownFunctionCriteria(keys=frozenset(known_exact_keys)),
                    exclude_known=sol_name in config.exclude_known,
                )
            if len(matches) > 1:
                names = [info.func.name for info in matches]
                raise ParseError(
                    f"Multiple Yul functions match '{sol_name}': {names}. "
                    f"Rename wrapper functions to avoid collisions "
                    f"(e.g. prefix with 'wrap_')."
                )
            match = matches[0]
            resolved_positions[sol_name] = (
                match.func.span.start,
                match.func.name,
                match.lexical_path,
            )
        known_exact_keys.add(
            FunctionKey(
                group_idx=syntax_info_by_token_idx[resolved_positions[sol_name][0]].group_idx,
                token_idx=resolved_positions[sol_name][0],
            )
        )

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
            resolved_group=index.resolved_groups[group_idx],
            syntax_index=index.syntax_indexes[group_idx],
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
        parsed_groups=index.parsed_groups,
        resolved_groups=index.resolved_groups,
        syntax_indexes=index.syntax_indexes,
        selected_functions=tuple(selected),
        target_infos=target_infos,
    )


def find_function_match(
    tokens: list[tuple[str, str]],
    sol_fn_name: str,
    *,
    n_params: int | None = None,
    known_yul_names: set[str] | None = None,
    exclude_known: bool = False,
    builtins: frozenset[str] = frozenset(),
) -> tuple[int, tuple[str, ...]]:
    index = _build_selection_index(tokens, builtins=builtins)
    matches = index.wrapper_matches(sol_fn_name, n_params=n_params)

    if not matches:
        if n_params is not None:
            prefixed = index.wrapper_matches(sol_fn_name)
            if prefixed:
                raise ParseError(
                    f"No Yul function for {sol_fn_name!r} matches "
                    f"{n_params} parameter(s)"
                )
        raise ParseError(
            f"Yul function for '{sol_fn_name}' not found "
            f"(expected pattern fun_{sol_fn_name}_<digits>)"
        )

    if known_yul_names and len(matches) > 1:
        matches = index.disambiguate_by_references(
            matches,
            known=_KnownFunctionCriteria(names=frozenset(known_yul_names)),
            exclude_known=exclude_known,
        )

    if len(matches) > 1:
        names = [info.func.name for info in matches]
        raise ParseError(
            f"Multiple Yul functions match '{sol_fn_name}': {names}. "
            f"Rename wrapper functions to avoid collisions "
            f"(e.g. prefix with 'wrap_')."
        )

    match = matches[0]
    return match.func.span.start, match.lexical_path


def find_exact_function_match(
    tokens: list[tuple[str, str]],
    yul_name: str,
    *,
    n_params: int | None = None,
    search_nested: bool = False,
    builtins: frozenset[str] = frozenset(),
) -> tuple[int, tuple[str, ...]]:
    index = _build_selection_index(tokens, builtins=builtins)
    matches = index.exact_matches(
        yul_name,
        n_params=n_params,
        search_nested=search_nested,
    )
    if not matches:
        if n_params is None:
            raise ParseError(f"Exact Yul function {yul_name!r} not found")
        raise ParseError(
            f"Exact Yul function {yul_name!r} with {n_params} parameter(s) not found"
        )
    if len(matches) > 1:
        qualified = ["::".join(info.lexical_path) for info in matches]
        raise ParseError(
            f"Multiple exact Yul functions matched {yul_name!r}: {qualified}. "
            "Use a scope-qualified exact_yul_names entry such as '::name' "
            "for a top-level function or 'outer::inner' for a nested one."
        )
    match = matches[0]
    return match.func.span.start, match.lexical_path


def find_exact_function_path_match(
    tokens: list[tuple[str, str]],
    yul_path: tuple[str, ...],
    *,
    n_params: int | None = None,
    builtins: frozenset[str] = frozenset(),
) -> tuple[int, tuple[str, ...]]:
    if not yul_path:
        raise ParseError("Exact Yul function path cannot be empty")
    index = _build_selection_index(tokens, builtins=builtins)
    matches = [
        info
        for info in index.exact_matches(
            yul_path[-1],
            n_params=n_params,
            search_nested=True,
        )
        if info.lexical_path == yul_path
    ]
    rendered = "::".join(yul_path)
    if not matches:
        if n_params is None:
            raise ParseError(f"Exact Yul function path {rendered!r} not found")
        raise ParseError(
            f"Exact Yul function path {rendered!r} with {n_params} parameter(s) not found"
        )
    if len(matches) > 1:
        raise ParseError(
            f"Multiple exact Yul functions matched path {rendered!r}. "
            "Refuse to guess."
        )
    match = matches[0]
    return match.func.span.start, match.lexical_path
