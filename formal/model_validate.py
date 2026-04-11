from __future__ import annotations

import re
from typing import assert_never

from evm_builtins import MODELED_BUILTIN_ARITY, OP_TO_LEAN_HELPER
from model_helpers import _expr_vars, _walk_model_exprs_in_stmt
from model_ir import (
    Assignment,
    Call,
    ConditionalBlock,
    Expr,
    FunctionModel,
    IntLit,
    Ite,
    ModelStatement,
    Project,
    Var,
)

from yul_ast import ParseError


def _validate_identifier(name: str, *, what: str) -> None:
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
        raise ParseError(f"Invalid {what}: {name!r}")


def validate_function_model(model: FunctionModel) -> None:
    """Reject malformed restricted-IR models."""

    _validate_identifier(model.fn_name, what="model name")
    if len(set(model.param_names)) != len(model.param_names):
        raise ParseError(
            f"Model {model.fn_name!r} has duplicate param names: {model.param_names!r}"
        )
    if len(set(model.return_names)) != len(model.return_names):
        raise ParseError(
            f"Model {model.fn_name!r} has duplicate return names: {model.return_names!r}"
        )
    if model.fn_name in OP_TO_LEAN_HELPER:
        raise ParseError(f"Model name {model.fn_name!r} collides with builtin opcode")
    if not model.return_names:
        raise ParseError(
            f"Model {model.fn_name!r} has no return variables; "
            f"restricted-IR functions must return at least one value"
        )
    for name in model.param_names:
        _validate_identifier(name, what=f"param name in {model.fn_name!r}")
    for name in model.return_names:
        _validate_identifier(name, what=f"return name in {model.fn_name!r}")

    def _validate_decl_binders_in_stmts(stmts: tuple[ModelStatement, ...]) -> None:
        for s in stmts:
            if isinstance(s, Assignment):
                _validate_identifier(
                    s.target, what=f"assignment target in {model.fn_name!r}"
                )
            elif isinstance(s, ConditionalBlock):
                for var in s.output_vars:
                    _validate_identifier(
                        var, what=f"conditional output var in {model.fn_name!r}"
                    )
                if len(set(s.output_vars)) != len(s.output_vars):
                    raise ParseError(
                        f"Model {model.fn_name!r} has duplicate conditional "
                        f"output_vars: {s.output_vars!r}"
                    )
                _validate_decl_binders_in_stmts(s.then_branch.assignments)
                _validate_decl_binders_in_stmts(s.else_branch.assignments)

    _validate_decl_binders_in_stmts(model.assignments)

    def _validate_expr_shape(expr: Expr) -> None:
        if isinstance(expr, Var):
            return
        if isinstance(expr, IntLit):
            if expr.value < 0:
                raise ParseError(
                    f"Model {model.fn_name!r}: IntLit({expr.value}) is negative "
                    f"(Yul integers are unsigned)"
                )
            return
        if isinstance(expr, Ite):
            _validate_expr_shape(expr.cond)
            _validate_expr_shape(expr.if_true)
            _validate_expr_shape(expr.if_false)
            return
        if isinstance(expr, Project):
            if not isinstance(expr.inner, Call):
                raise ParseError(
                    f"Model {model.fn_name!r}: Project({expr.index}, {expr.total}) inner "
                    f"must be a Call, got {type(expr.inner).__name__}"
                )
            if expr.index < 0 or expr.index >= expr.total:
                raise ParseError(
                    f"Model {model.fn_name!r}: Project({expr.index}, {expr.total}) index "
                    f"{expr.index} out of range [0, {expr.total})"
                )
            if expr.total < 2:
                raise ParseError(
                    f"Model {model.fn_name!r}: Project({expr.index}, {expr.total}) "
                    f"requires total >= 2 (scalar values cannot be projected)"
                )
            if expr.inner.name in OP_TO_LEAN_HELPER:
                raise ParseError(
                    f"Model {model.fn_name!r}: cannot project builtin "
                    f"{expr.inner.name!r} (returns scalar, not tuple)"
                )
            _validate_expr_shape(expr.inner)
            return
        if not isinstance(expr, Call):
            assert_never(expr)
        if expr.name in OP_TO_LEAN_HELPER:
            expected = MODELED_BUILTIN_ARITY[expr.name]
            if len(expr.args) != expected:
                raise ParseError(
                    f"Model {model.fn_name!r}: builtin {expr.name!r} expects "
                    f"{expected} arg(s), got {len(expr.args)}"
                )
        for arg in expr.args:
            _validate_expr_shape(arg)

    def _validate_expr_shapes_in_stmt(s: ModelStatement) -> None:
        if isinstance(s, Assignment):
            _validate_expr_shape(s.expr)
        elif isinstance(s, ConditionalBlock):
            _validate_expr_shape(s.condition)
            for sub in s.then_branch.assignments:
                _validate_expr_shapes_in_stmt(sub)
            for sub in s.else_branch.assignments:
                _validate_expr_shapes_in_stmt(sub)

    def _validate_statement_block(
        statements: tuple[ModelStatement, ...],
        *,
        available: set[str],
        block_name: str,
    ) -> set[str]:
        scope = set(available)
        for s in statements:
            if isinstance(s, Assignment):
                _validate_expr_shape(s.expr)
                missing = _expr_vars(s.expr) - scope
                if missing:
                    raise ParseError(
                        f"Model {model.fn_name!r} has an out-of-scope variable "
                        f"use in {block_name}: {s.target!r} depends on "
                        f"{sorted(missing)}"
                    )
                scope.add(s.target)
            elif isinstance(s, ConditionalBlock):
                _validate_conditional_in_scope(s, scope=scope, block_name=block_name)
                scope.update(s.output_vars)
        return scope

    def _validate_conditional_in_scope(
        cond: ConditionalBlock,
        *,
        scope: set[str],
        block_name: str,
    ) -> None:
        _validate_expr_shape(cond.condition)
        for s in cond.then_branch.assignments:
            _validate_expr_shapes_in_stmt(s)
        for s in cond.else_branch.assignments:
            _validate_expr_shapes_in_stmt(s)
        missing = _expr_vars(cond.condition) - scope
        if missing:
            raise ParseError(
                f"Model {model.fn_name!r} has an out-of-scope conditional: "
                f"{sorted(missing)}"
            )
        for label, branch in [
            ("then-branch", cond.then_branch),
            ("else-branch", cond.else_branch),
        ]:
            branch_scope = _validate_statement_block(
                branch.assignments,
                available=scope,
                block_name=f"{block_name}/{label}",
            )
            if len(branch.outputs) != len(cond.output_vars):
                raise ParseError(
                    f"Model {model.fn_name!r} has mismatched {label} output "
                    f"arity: {len(branch.outputs)} vs {len(cond.output_vars)}"
                )
            for out_expr in branch.outputs:
                _validate_expr_shape(out_expr)
                missing_out = _expr_vars(out_expr) - branch_scope
                if missing_out:
                    raise ParseError(
                        f"Model {model.fn_name!r} has undefined {label} outputs: "
                        f"{sorted(missing_out)}"
                    )

    scope = _validate_statement_block(
        model.assignments,
        available=set(model.param_names),
        block_name="top-level",
    )

    missing_returns = set(model.return_names) - scope
    if missing_returns:
        raise ParseError(
            f"Model {model.fn_name!r} returns undefined vars: {sorted(missing_returns)}"
        )


def validate_model_set(models: list[FunctionModel]) -> None:
    """Validate a model set structurally and across its call graph."""

    for model in models:
        validate_function_model(model)

    seen_names: set[str] = set()
    for model in models:
        if model.fn_name in seen_names:
            raise ParseError(f"Duplicate selected function {model.fn_name!r}")
        seen_names.add(model.fn_name)

    sig_table = {
        model.fn_name: (len(model.param_names), len(model.return_names))
        for model in models
    }

    def _check_calls(expr: Expr, model_fn_name: str) -> set[str]:
        callees: set[str] = set()
        if isinstance(expr, (IntLit, Var)):
            return callees
        if isinstance(expr, Ite):
            callees.update(_check_calls(expr.cond, model_fn_name))
            callees.update(_check_calls(expr.if_true, model_fn_name))
            callees.update(_check_calls(expr.if_false, model_fn_name))
            return callees
        if isinstance(expr, Project):
            inner = expr.inner
            if isinstance(inner, Call) and inner.name in sig_table:
                callees.add(inner.name)
                _, callee_rets = sig_table[inner.name]
                if callee_rets != expr.total:
                    raise ParseError(
                        f"Model {model_fn_name!r}: Project({expr.index}, {expr.total}) "
                        f"expects {expr.total} return values from {inner.name!r}, "
                        f"but it returns {callee_rets}"
                    )
                if callee_rets < 2:
                    raise ParseError(
                        f"Model {model_fn_name!r}: cannot project "
                        f"{inner.name!r} which returns {callee_rets} value(s) "
                        f"(need >= 2 for projection)"
                    )
                callee_params, _ = sig_table[inner.name]
                if len(inner.args) != callee_params:
                    raise ParseError(
                        f"Model {model_fn_name!r}: call to {inner.name!r} "
                        f"passes {len(inner.args)} arg(s), expected {callee_params}"
                    )
                for a in inner.args:
                    callees.update(_check_calls(a, model_fn_name))
            else:
                callees.update(_check_calls(inner, model_fn_name))
            return callees
        if not isinstance(expr, Call):
            assert_never(expr)

        if expr.name in sig_table:
            callees.add(expr.name)
            callee_params, callee_rets = sig_table[expr.name]
            if len(expr.args) != callee_params:
                raise ParseError(
                    f"Model {model_fn_name!r}: call to {expr.name!r} passes "
                    f"{len(expr.args)} arg(s), expected {callee_params}"
                )
            if callee_rets > 1:
                raise ParseError(
                    f"Model {model_fn_name!r}: multi-return function "
                    f"{expr.name!r} ({callee_rets} returns) used in scalar "
                    f"context without Project projection"
                )
        elif expr.name not in OP_TO_LEAN_HELPER:
            raise ParseError(
                f"Model {model_fn_name!r}: unresolved call target {expr.name!r}"
            )

        for a in expr.args:
            callees.update(_check_calls(a, model_fn_name))
        return callees

    call_graph: dict[str, set[str]] = {m.fn_name: set() for m in models}

    def _collect_calls_from_stmt(
        stmt: ModelStatement,
        fn_name: str,
        out: set[str],
    ) -> None:
        _walk_model_exprs_in_stmt(
            stmt,
            lambda expr: out.update(_check_calls(expr, fn_name)),
        )

    for model in models:
        for stmt in model.assignments:
            _collect_calls_from_stmt(stmt, model.fn_name, call_graph[model.fn_name])

    WHITE, GRAY, BLACK = 0, 1, 2
    color: dict[str, int] = {name: WHITE for name in call_graph}

    def _dfs(node: str, path: list[str]) -> None:
        color[node] = GRAY
        path.append(node)
        for callee in call_graph[node]:
            if callee not in color:
                continue
            if color[callee] == GRAY:
                cycle_start = path.index(callee)
                cycle = path[cycle_start:]
                raise ParseError(
                    f"Cycle detected among selected models: "
                    f"{' → '.join(cycle)} → {callee}"
                )
            if color[callee] == WHITE:
                _dfs(callee, path)
        path.pop()
        color[node] = BLACK

    for name in call_graph:
        if color[name] == WHITE:
            _dfs(name, [])
