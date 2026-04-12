from __future__ import annotations

from dataclasses import dataclass
from typing import assert_never

from .evm_builtins import BASE_NORM_HELPERS as _BASE_NORM_HELPERS
from .evm_builtins import MODELED_BUILTINS, OP_TO_LEAN_HELPER, WORD_MOD
from .lean_names import (
    BASE_RESERVED_LEAN_NAMES,
    norm_reserved_lean_names,
    reserved_model_binder_names,
    validate_ident,
)
from .model_config import EmissionConfig, TransformConfig
from .model_helpers import (
    collect_model_binders,
    collect_model_opcodes,
    model_call_names_in_stmt,
)
from .model_ir import (
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
from .model_validate import validate_model_set
from .yul_ast import ParseError


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
        args = " ".join(
            f"({emit_expr(arg, helper_map=helper_map)})" for arg in expr.args
        )
        return f"{helper} {args}".rstrip()
    assert_never(expr)


def build_model_body(
    assignments: tuple[ModelStatement, ...],
    *,
    evm: bool,
    emission: EmissionConfig,
    param_names: tuple[str, ...] = ("x",),
    return_names: tuple[str, ...] = ("z",),
    call_map: dict[str, str] | None = None,
) -> str:
    emission_config = emission
    lines: list[str] = []
    norm_helpers = {**_BASE_NORM_HELPERS, **emission_config.norm_helper_map()}

    if evm:
        for name in param_names:
            lines.append(f"  let {name} := u256 {name}")
        helper_map = OP_TO_LEAN_HELPER
    else:
        helper_map = norm_helpers

    merged_map = {**helper_map, **(call_map or {})}

    def emit_rhs(expr: Expr) -> str:
        rendered = (
            emission_config.norm_rewrite(expr)
            if not evm and emission_config.norm_rewrite
            else expr
        )
        return emit_expr(rendered, helper_map=merged_map)

    def emit_name_tuple(names: tuple[str, ...]) -> str:
        if len(names) == 1:
            return names[0]
        return f"({', '.join(names)})"

    def emit_expr_tuple(exprs: tuple[Expr, ...]) -> str:
        parts = [emit_rhs(expr) for expr in exprs]
        if len(parts) == 1:
            return parts[0]
        return f"({', '.join(parts)})"

    def emit_stmts(stmts: tuple[ModelStatement, ...], indent: int) -> None:
        prefix = " " * indent
        for stmt in stmts:
            if isinstance(stmt, Assignment):
                lines.append(f"{prefix}let {stmt.target} := {emit_rhs(stmt.expr)}")
            elif isinstance(stmt, ConditionalBlock):
                lhs = emit_name_tuple(stmt.output_vars)
                condition = emit_rhs(stmt.condition)
                lines.append(f"{prefix}let {lhs} := if ({condition}) ≠ 0 then")
                emit_stmts(stmt.then_branch.assignments, indent + 4)
                lines.append(f"{prefix}    {emit_expr_tuple(stmt.then_branch.outputs)}")
                lines.append(f"{prefix}  else")
                emit_stmts(stmt.else_branch.assignments, indent + 4)
                lines.append(f"{prefix}    {emit_expr_tuple(stmt.else_branch.outputs)}")
            else:
                assert_never(stmt)

    emit_stmts(assignments, indent=2)
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


def any_norm_models(
    models: list[FunctionModel],
    transforms: TransformConfig,
) -> bool:
    return any(model.fn_name not in transforms.skip_norm for model in models)


def _plan_emitted_model_defs(
    function_names: tuple[str, ...],
    emission: EmissionConfig,
    transforms: TransformConfig,
) -> tuple[EmittedModelDef, ...]:
    planned: list[EmittedModelDef] = []
    for fn_name in function_names:
        base_name = emission.model_names.get(fn_name)
        if base_name is None:
            raise ParseError(f"Model {fn_name!r} has no entry in emission.model_names")
        planned.append(
            EmittedModelDef(
                fn_name=fn_name,
                base_name=base_name,
                evm_name=f"{base_name}_evm",
                emit_norm=fn_name not in transforms.skip_norm,
            )
        )
    return tuple(planned)


def _build_lean_emission_plan(
    models: list[FunctionModel],
    emission: EmissionConfig,
    transforms: TransformConfig,
) -> LeanEmissionPlan:
    emit_any_norm = any_norm_models(models, transforms)
    extra_norm_names = emission.norm_helper_names()
    norm_reserved = (
        norm_reserved_lean_names(extra_norm_names) if emit_any_norm else frozenset()
    )
    builtin_helper_names = BASE_RESERVED_LEAN_NAMES | norm_reserved

    planned_defs = _plan_emitted_model_defs(
        tuple(model.fn_name for model in models),
        emission,
        transforms,
    )
    planned_by_name = {planned.fn_name: planned for planned in planned_defs}

    model_defs: list[EmittedModelDef] = []
    generated_def_names: set[str] = set()
    for planned in planned_defs:
        if planned.emit_norm:
            validate_ident(
                planned.base_name, what=f"generated model name for {planned.fn_name!r}"
            )
        validate_ident(
            planned.evm_name, what=f"generated EVM model name for {planned.fn_name!r}"
        )

        if planned.emit_norm and planned.base_name in builtin_helper_names:
            raise ParseError(
                f"Reserved name used as model name for {planned.fn_name!r}: "
                f"{planned.base_name!r}"
            )
        if planned.evm_name in builtin_helper_names:
            raise ParseError(
                f"Generated model name {planned.evm_name!r} collides with a builtin "
                f"helper or reserved name"
            )

        if planned.emit_norm and planned.base_name in generated_def_names:
            raise ParseError(f"Duplicate generated model name {planned.base_name!r}")
        if planned.evm_name in generated_def_names:
            raise ParseError(f"Duplicate generated EVM model name {planned.evm_name!r}")

        if planned.emit_norm:
            generated_def_names.add(planned.base_name)
        generated_def_names.add(planned.evm_name)
        model_defs.append(planned)

    for model in models:
        planned = planned_by_name[model.fn_name]
        if not planned.emit_norm:
            continue
        skipped_norm_callees = sorted(
            callee
            for stmt in model.assignments
            for callee in model_call_names_in_stmt(stmt)
            if callee in planned_by_name and not planned_by_name[callee].emit_norm
        )
        if skipped_norm_callees:
            skipped_list = ", ".join(repr(name) for name in skipped_norm_callees)
            raise ParseError(
                f"Cannot emit norm model for {model.fn_name!r}: "
                f"calls skipped norm callee(s) {skipped_list}"
            )

    return LeanEmissionPlan(
        emit_any_norm=emit_any_norm,
        model_defs=tuple(model_defs),
    )


def render_function_defs(
    models: list[FunctionModel],
    emission: EmissionConfig,
    transforms: TransformConfig,
    *,
    emission_plan: LeanEmissionPlan | None = None,
) -> str:
    emission_config, transform_config = emission, transforms
    validate_model_set(models)

    if emission_plan is None:
        emission_plan = _build_lean_emission_plan(
            models,
            emission_config,
            transform_config,
        )
    if len(emission_plan.model_defs) != len(models):
        raise ParseError("Lean emission plan/model count mismatch")

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
            raise ParseError("Lean emission plan/model order mismatch")

        evm_body = build_model_body(
            model.assignments,
            evm=True,
            emission=emission_config,
            param_names=model.param_names,
            return_names=model.return_names,
            call_map=evm_call_map,
        )
        param_sig = (
            f" ({' '.join(model.param_names)} : Nat)" if model.param_names else ""
        )
        ret_type = (
            "Nat"
            if len(model.return_names) == 1
            else " × ".join("Nat" for _ in model.return_names)
        )
        parts.append(
            f"/-- Opcode-faithful auto-generated model of `{model.fn_name}` with uint256 EVM semantics. -/\n"
            f"def {planned.evm_name}{param_sig} : {ret_type} :=\n"
            f"{evm_body}\n"
        )

        if planned.emit_norm:
            norm_body = build_model_body(
                model.assignments,
                evm=False,
                emission=emission_config,
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


def build_lean_source(
    *,
    models: list[FunctionModel],
    source_path: str,
    namespace: str,
    emission: EmissionConfig,
    transforms: TransformConfig = TransformConfig(),
) -> str:
    emission_config, transform_config = emission, transforms
    validate_ident(namespace, what="Lean namespace")
    if "\n" in source_path:
        raise ParseError(
            f"Source path contains newline (potential injection): {source_path!r}"
        )
    if "\n" in emission_config.generator_label:
        raise ParseError(
            f"Generator label contains newline (potential injection): "
            f"{emission_config.generator_label!r}"
        )
    if "-/" in emission_config.header_comment:
        raise ParseError(
            f"Header comment contains Lean doc-comment terminator '-/': "
            f"{emission_config.header_comment!r}"
        )

    validate_model_set(models)
    emission_plan = _build_lean_emission_plan(
        models,
        emission_config,
        transform_config,
    )
    binder_reserved = reserved_model_binder_names(
        tuple(model.fn_name for model in models),
        emission_config,
        transform_config,
    )

    for model in models:
        for binder in collect_model_binders(model):
            validate_ident(
                binder,
                what=f"binder in model {model.fn_name!r}",
                extra_reserved=binder_reserved,
            )

    modeled_functions = ", ".join(model.fn_name for model in models)
    opcodes_line = ", ".join(collect_model_opcodes(models))
    function_defs = render_function_defs(
        models,
        emission_config,
        transform_config,
        emission_plan=emission_plan,
    )

    evm_defs = "\n\n".join(spec.evm_def for spec in MODELED_BUILTINS) + "\n\n"
    norm_defs = ""
    if emission_plan.emit_any_norm:
        norm_parts = [spec.norm_def for spec in MODELED_BUILTINS]
        norm_parts.extend(
            extension.lean_def.rstrip()
            for extension in emission_config.norm_extensions
            if extension.lean_def.strip()
        )
        norm_defs = "\n\n".join(norm_parts) + "\n\n"

    return (
        "import Init\n\n"
        f"namespace {namespace}\n\n"
        f"/-- {emission_config.header_comment} -/\n"
        f"-- Source: {source_path}\n"
        f"-- Modeled functions: {modeled_functions}\n"
        f"-- Generated by: {emission_config.generator_label}\n"
        f"-- Modeled opcodes/Yul builtins: {opcodes_line}\n\n"
        "def WORD_MOD : Nat := 2 ^ 256\n\n"
        "def u256 (x : Nat) : Nat :=\n"
        "  x % WORD_MOD\n\n"
        f"{evm_defs}"
        f"{norm_defs}"
        f"{function_defs}\n"
        f"end {namespace}\n"
    )
