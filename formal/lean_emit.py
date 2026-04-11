from __future__ import annotations

import re
from dataclasses import dataclass
from typing import assert_never

from evm_builtins import BASE_NORM_HELPERS as _BASE_NORM_HELPERS
from evm_builtins import (
    MODELED_BUILTINS,
    OP_TO_LEAN_HELPER,
    WORD_MOD,
)
from lean_names import (
    BASE_RESERVED_LEAN_NAMES,
    norm_reserved_lean_names,
    validate_ident,
)
from model_config import ModelConfig
from model_helpers import (
    _collect_model_binders,
    _model_call_names_in_stmt,
    collect_model_opcodes,
)
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
from model_validate import validate_model_set

from yul_ast import ParseError


def emit_expr(
    expr: Expr,
    *,
    helper_map: dict[str, str],
) -> str:
    if isinstance(expr, IntLit):
        return str(expr.value % WORD_MOD)
    if isinstance(expr, Var):
        return expr.name
    if isinstance(expr, Project):
        idx = expr.index
        total = expr.total
        inner = emit_expr(expr.inner, helper_map=helper_map)
        if total <= 2 or idx == 0:
            return f"({inner}).{idx + 1}"
        if idx == total - 1:
            return f"({inner})" + ".2" * idx
        return f"({inner})" + ".2" * idx + ".1"
    if isinstance(expr, Ite):
        cond = emit_expr(expr.cond, helper_map=helper_map)
        if_val = emit_expr(expr.if_true, helper_map=helper_map)
        else_val = emit_expr(expr.if_false, helper_map=helper_map)
        return f"if ({cond}) ≠ 0 then {if_val} else {else_val}"
    if isinstance(expr, Call):
        helper = helper_map.get(expr.name)
        if helper is None:
            raise ParseError(f"Unsupported call in Lean emitter: {expr.name!r}")
        args = " ".join(f"({emit_expr(a, helper_map=helper_map)})" for a in expr.args)
        return f"{helper} {args}".rstrip()
    assert_never(expr)


def build_model_body(
    assignments: tuple[ModelStatement, ...],
    *,
    evm: bool,
    config: ModelConfig,
    param_names: tuple[str, ...] = ("x",),
    return_names: tuple[str, ...] = ("z",),
    call_map: dict[str, str] | None = None,
) -> str:
    lines: list[str] = []
    norm_helpers = {**_BASE_NORM_HELPERS, **config.extra_norm_ops}

    if evm:
        for p in param_names:
            lines.append(f"  let {p} := u256 {p}")
        op_map = OP_TO_LEAN_HELPER
    else:
        op_map = norm_helpers

    merged_map = {**op_map, **(call_map or {})}

    def _emit_rhs(expr: Expr) -> str:
        rhs_expr = expr
        if not evm and config.norm_rewrite is not None:
            rhs_expr = config.norm_rewrite(rhs_expr)
        return emit_expr(rhs_expr, helper_map=merged_map)

    def _emit_name_tuple(vars_: tuple[str, ...]) -> str:
        if len(vars_) == 1:
            return vars_[0]
        return f"({', '.join(vars_)})"

    def _emit_expr_tuple(exprs: tuple[Expr, ...]) -> str:
        parts = [_emit_rhs(e) for e in exprs]
        if len(parts) == 1:
            return parts[0]
        return f"({', '.join(parts)})"

    def _emit_stmts(stmts: tuple[ModelStatement, ...], indent: int) -> None:
        prefix = " " * indent
        for stmt in stmts:
            if isinstance(stmt, Assignment):
                rhs = _emit_rhs(stmt.expr)
                lines.append(f"{prefix}let {stmt.target} := {rhs}")
            elif isinstance(stmt, ConditionalBlock):
                cond_str = _emit_rhs(stmt.condition)
                lhs = _emit_name_tuple(stmt.output_vars)
                lines.append(f"{prefix}let {lhs} := if ({cond_str}) ≠ 0 then")
                _emit_stmts(stmt.then_branch.assignments, indent + 4)
                lines.append(
                    f"{prefix}    {_emit_expr_tuple(stmt.then_branch.outputs)}"
                )
                lines.append(f"{prefix}  else")
                _emit_stmts(stmt.else_branch.assignments, indent + 4)
                lines.append(
                    f"{prefix}    {_emit_expr_tuple(stmt.else_branch.outputs)}"
                )
            else:
                assert_never(stmt)

    _emit_stmts(assignments, indent=2)

    if len(return_names) == 1:
        lines.append(f"  {return_names[0]}")
    else:
        lines.append(f"  ({', '.join(return_names)})")
    return "\n".join(lines)


@dataclass(frozen=True)
class EmittedModelDef:
    fn_name: str
    base_name: str
    evm_name: str
    emit_norm: bool


@dataclass(frozen=True)
class LeanEmissionPlan:
    emit_any_norm: bool
    model_defs: tuple[EmittedModelDef, ...]
    generated_def_names: frozenset[str]
    extra_norm_binder_names: frozenset[str]


def _plan_emitted_model_defs(
    function_names: tuple[str, ...],
    config: ModelConfig,
) -> tuple[EmittedModelDef, ...]:
    planned: list[EmittedModelDef] = []
    for fn_name in function_names:
        base_name = config.model_names.get(fn_name)
        if base_name is None:
            raise ParseError(f"Model {fn_name!r} has no entry in config.model_names")
        planned.append(
            EmittedModelDef(
                fn_name=fn_name,
                base_name=base_name,
                evm_name=f"{base_name}_evm",
                emit_norm=fn_name not in config.skip_norm,
            )
        )
    return tuple(planned)


def _build_lean_emission_plan(
    models: list[FunctionModel],
    config: ModelConfig,
) -> LeanEmissionPlan:
    emit_any_norm = any_norm_models(models, config)
    base_reserved = BASE_RESERVED_LEAN_NAMES
    norm_reserved = (
        norm_reserved_lean_names(config.extra_norm_ops)
        if emit_any_norm
        else frozenset()
    )
    builtin_helper_names = base_reserved | norm_reserved

    planned_defs = _plan_emitted_model_defs(
        tuple(model.fn_name for model in models),
        config,
    )
    planned_by_name = {planned.fn_name: planned for planned in planned_defs}
    model_defs: list[EmittedModelDef] = []
    generated_def_names: set[str] = set()
    for planned in planned_defs:
        base_name = planned.base_name
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", base_name):
            raise ParseError(
                f"Invalid generated model name for {planned.fn_name!r}: {base_name!r}"
            )

        reserved_names = base_reserved | (
            norm_reserved if planned.emit_norm else frozenset()
        )
        if base_name in reserved_names:
            raise ParseError(
                f"Reserved name used as model name for {planned.fn_name!r}: "
                f"{base_name!r}"
            )

        evm_name = planned.evm_name
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", evm_name):
            raise ParseError(f"Invalid generated EVM model name: {evm_name!r}")
        if planned.emit_norm and base_name in generated_def_names:
            raise ParseError(f"Duplicate generated model name {base_name!r}")
        if evm_name in generated_def_names:
            raise ParseError(f"Duplicate generated EVM model name {evm_name!r}")

        if planned.emit_norm:
            generated_def_names.add(base_name)
        generated_def_names.add(evm_name)
        model_defs.append(planned)

    for model in models:
        planned = planned_by_name[model.fn_name]
        if not planned.emit_norm:
            continue
        skipped_norm_callees = sorted(
            callee
            for stmt in model.assignments
            for callee in _model_call_names_in_stmt(stmt)
            if callee in planned_by_name and not planned_by_name[callee].emit_norm
        )
        if skipped_norm_callees:
            skipped_list = ", ".join(repr(name) for name in skipped_norm_callees)
            raise ParseError(
                f"Cannot emit norm model for {model.fn_name!r}: "
                f"calls skipped norm callee(s) {skipped_list}"
            )

    for name in generated_def_names:
        if name in builtin_helper_names:
            raise ParseError(
                f"Generated model name {name!r} collides with a builtin "
                f"helper or reserved name"
            )

    return LeanEmissionPlan(
        emit_any_norm=emit_any_norm,
        model_defs=tuple(model_defs),
        generated_def_names=frozenset(generated_def_names),
        extra_norm_binder_names=frozenset(config.extra_norm_ops.values()),
    )


def render_function_defs(
    models: list[FunctionModel],
    config: ModelConfig,
    *,
    emission_plan: LeanEmissionPlan | None = None,
) -> str:
    validate_model_set(models)

    if emission_plan is None:
        emission_plan = _build_lean_emission_plan(models, config)
    if len(emission_plan.model_defs) != len(models):
        raise ParseError(
            "Lean emission plan/model count mismatch. Refuse to render "
            "with inconsistent emitted names."
        )

    parts: list[str] = []
    evm_call_map = {
        planned.fn_name: planned.evm_name for planned in emission_plan.model_defs
    }
    norm_call_map = {
        planned.fn_name: planned.base_name
        for planned in emission_plan.model_defs
        if planned.emit_norm
    }
    for model, planned in zip(models, emission_plan.model_defs):
        if planned.fn_name != model.fn_name:
            raise ParseError(
                "Lean emission plan/model order mismatch. Refuse to render "
                "with inconsistent emitted names."
            )
        evm_body = build_model_body(
            model.assignments,
            evm=True,
            config=config,
            param_names=model.param_names,
            return_names=model.return_names,
            call_map=evm_call_map,
        )

        if model.param_names:
            param_sig = f" ({' '.join(model.param_names)} : Nat)"
        else:
            param_sig = ""
        if len(model.return_names) == 1:
            ret_type = "Nat"
        else:
            ret_type = " × ".join("Nat" for _ in model.return_names)
        parts.append(
            f"/-- Opcode-faithful auto-generated model of `{model.fn_name}` with uint256 EVM semantics. -/\n"
            f"def {planned.evm_name}{param_sig} : {ret_type} :=\n"
            f"{evm_body}\n"
        )
        if planned.emit_norm:
            norm_body = build_model_body(
                model.assignments,
                evm=False,
                config=config,
                param_names=model.param_names,
                return_names=model.return_names,
                call_map=norm_call_map,
            )
            parts.append(
                f"/-- Normalized auto-generated model of `{model.fn_name}` on Nat arithmetic. -/\n"
                f"def {planned.base_name}{param_sig} : {ret_type} :=\n"
                f"{norm_body}\n"
            )
    return "\n".join(parts)


def any_norm_models(models: list[FunctionModel], config: ModelConfig) -> bool:
    return any(m.fn_name not in config.skip_norm for m in models)


def build_lean_source(
    *,
    models: list[FunctionModel],
    source_path: str,
    namespace: str,
    config: ModelConfig,
) -> str:
    validate_ident(namespace, what="Lean namespace")

    if "\n" in source_path:
        raise ParseError(
            f"Source path contains newline (potential injection): {source_path!r}"
        )
    if "\n" in config.generator_label:
        raise ParseError(
            f"Generator label contains newline (potential injection): "
            f"{config.generator_label!r}"
        )
    if "-/" in config.header_comment:
        raise ParseError(
            f"Header comment contains Lean doc-comment terminator '-/': "
            f"{config.header_comment!r}"
        )

    validate_model_set(models)

    emission_plan = _build_lean_emission_plan(models, config)

    def _check_binder_collision(binder: str, model_fn_name: str) -> None:
        if binder in emission_plan.generated_def_names:
            raise ParseError(
                f"Binder {binder!r} in model {model_fn_name!r} collides "
                f"with a generated model def name"
            )

    for model in models:
        for binder in _collect_model_binders(model):
            _check_binder_collision(binder, model.fn_name)

    if emission_plan.extra_norm_binder_names:
        for model, planned in zip(models, emission_plan.model_defs):
            if not planned.emit_norm:
                continue
            for binder in _collect_model_binders(model):
                if binder in emission_plan.extra_norm_binder_names:
                    raise ParseError(
                        f"Reserved Lean helper name used as binder in "
                        f"{model.fn_name!r}: {binder!r}"
                    )

    modeled_functions = ", ".join(model.fn_name for model in models)
    opcodes = collect_model_opcodes(models)
    opcodes_line = ", ".join(opcodes)

    function_defs = render_function_defs(
        models,
        config,
        emission_plan=emission_plan,
    )

    extra_lean_defs = config.extra_lean_defs.rstrip() if config.extra_lean_defs else ""
    evm_defs = "\n\n".join(spec.evm_def for spec in MODELED_BUILTINS) + "\n\n"
    norm_defs = ""
    if emission_plan.emit_any_norm:
        norm_parts: list[str] = []
        for spec in MODELED_BUILTINS:
            norm_parts.append(spec.norm_def)
            if spec.name == "clz" and extra_lean_defs:
                norm_parts.append(extra_lean_defs)
        norm_defs = "\n\n".join(norm_parts) + "\n\n"

    return (
        "import Init\n\n"
        f"namespace {namespace}\n\n"
        f"/-- {config.header_comment} -/\n"
        f"-- Source: {source_path}\n"
        f"-- Modeled functions: {modeled_functions}\n"
        f"-- Generated by: {config.generator_label}\n"
        f"-- Modeled opcodes/Yul builtins: {opcodes_line}\n\n"
        "def WORD_MOD : Nat := 2 ^ 256\n\n"
        "def u256 (x : Nat) : Nat :=\n"
        "  x % WORD_MOD\n\n"
        f"{evm_defs}"
        f"{norm_defs}"
        f"{function_defs}\n"
        f"end {namespace}\n"
    )
