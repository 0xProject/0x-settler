"""
Centralized identifier policy for formal Python IRs and Lean emission.

This module owns:
- Lean-facing reserved names and lexical validation
- Yul-to-model demangling and binder sanitization
- module-wide function/binder name planning before SSA
- SSA suffix allocation for already-legalized binder bases
"""

from __future__ import annotations

import re
from collections import Counter
from collections.abc import Iterable
from dataclasses import dataclass, field

from .evm_builtins import BASE_NORM_HELPERS, OP_TO_LEAN_HELPER
from .model_config import EmissionConfig, TransformConfig
from .restricted_ir import (
    RAssignment,
    RCallAssign,
    RConditionalBlock,
    RestrictedFunction,
    RExpr,
    RModelCall,
    RRef,
    RStatement,
)
from .restricted_walk import (
    for_each_stmt,
)
from .restricted_walk import map_expr as _map_expr
from .restricted_walk import map_stmt as _map_stmt
from .yul_ast import EmissionError, SymbolId

# Conservative subset of the fixed builtin command/term keywords from Lean 4's
# default parser, used to keep generated names away from the surface syntax we
# emit against. We do not try to model extension-defined keywords here.
LEAN_KEYWORDS: frozenset[str] = frozenset(
    {
        "if",
        "then",
        "else",
        "let",
        "in",
        "do",
        "where",
        "match",
        "with",
        "fun",
        "return",
        "import",
        "open",
        "namespace",
        "end",
        "def",
        "theorem",
        "lemma",
        "example",
        "structure",
        "class",
        "instance",
        "section",
        "variable",
        "universe",
        "axiom",
        "inductive",
        "coinductive",
        "mutual",
        "partial",
        "unsafe",
        "private",
        "protected",
        "noncomputable",
        "macro",
        "syntax",
        "notation",
        "prefix",
        "infix",
        "infixl",
        "infixr",
        "postfix",
        "attribute",
        "deriving",
        "extends",
        "abbrev",
        "opaque",
        "set_option",
        "for",
        "true",
        "false",
        "Type",
        "Prop",
        "Sort",
    }
)

BASE_RESERVED_LEAN_NAMES: frozenset[str] = frozenset(
    {"u256", "WORD_MOD"} | set(OP_TO_LEAN_HELPER.values()) | LEAN_KEYWORDS
)
RESERVED_LEAN_NAMES: frozenset[str] = frozenset(
    set(BASE_RESERVED_LEAN_NAMES) | set(BASE_NORM_HELPERS.values())
)


def norm_reserved_lean_names(
    extra_helper_names: Iterable[str] = (),
) -> frozenset[str]:
    return frozenset(set(BASE_NORM_HELPERS.values()) | set(extra_helper_names))


@dataclass(frozen=True)
class EmittedModelDef:
    """One emitted Lean definition pair owned by the naming policy."""

    fn_name: str
    base_name: str
    evm_name: str
    emit_norm: bool


def plan_emitted_model_defs(
    function_names: tuple[str, ...],
    emission: EmissionConfig,
    transforms: TransformConfig,
) -> tuple[EmittedModelDef, ...]:
    """Plan emitted model names once for both reservation and emission."""

    planned: list[EmittedModelDef] = []
    for fn_name in function_names:
        base_name = emission.model_names.get(fn_name)
        if base_name is None:
            raise EmissionError(
                f"Model {fn_name!r} has no entry in emission.model_names"
            )
        planned.append(
            EmittedModelDef(
                fn_name=fn_name,
                base_name=base_name,
                evm_name=f"{base_name}_evm",
                emit_norm=fn_name not in transforms.skip_norm,
            )
        )
    return tuple(planned)


def _emitted_model_def_names(
    planned_defs: tuple[EmittedModelDef, ...],
) -> frozenset[str]:
    generated: set[str] = set()
    for planned in planned_defs:
        if planned.emit_norm:
            generated.add(planned.base_name)
        generated.add(planned.evm_name)
    return frozenset(generated)


def emitted_model_def_names(
    function_names: tuple[str, ...],
    emission: EmissionConfig,
    transforms: TransformConfig,
) -> frozenset[str]:
    return _emitted_model_def_names(
        plan_emitted_model_defs(function_names, emission, transforms)
    )


def reserved_model_binder_names(
    function_names: tuple[str, ...],
    emission: EmissionConfig,
    transforms: TransformConfig,
) -> frozenset[str]:
    planned_defs = plan_emitted_model_defs(function_names, emission, transforms)
    emit_any_norm = any(planned.emit_norm for planned in planned_defs)
    extra_norm_names = emission.norm_helper_names() if emit_any_norm else frozenset()
    reserved = set(BASE_RESERVED_LEAN_NAMES)
    if emit_any_norm:
        reserved.update(norm_reserved_lean_names(extra_norm_names))
    reserved.update(_emitted_model_def_names(planned_defs))
    return frozenset(reserved)


def validate_ident(
    name: str,
    *,
    what: str,
    extra_reserved: Iterable[str] = (),
) -> None:
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
        raise EmissionError(f"Invalid {what}: {name!r}")
    if name in RESERVED_LEAN_NAMES or name in set(extra_reserved):
        raise EmissionError(f"Reserved Lean helper name used as {what}: {name!r}")


def _demangle(name: str) -> str:
    """Demangle a Yul variable name to its Solidity-level name."""
    if name.startswith("usr$"):
        return name[4:]
    match = re.fullmatch(r"var_(\w+?)_\d+", name)
    if match:
        return match.group(1)
    return name


def _sanitize_base(name: str) -> str:
    """Ensure *name* is a syntactically valid identifier."""
    name = name.replace("$", "_").replace(".", "_")
    name = re.sub(r"[^A-Za-z0-9_]", "", name)
    if not name or (not name[0].isalpha() and name[0] != "_"):
        name = "_" + name if name else "_v"
    return name


def _legalize_identifier_base(name: str) -> str:
    """Demangle + sanitize a binder name."""
    return _sanitize_base(_demangle(name))


def _uniquify_name_bases(
    raw_names: dict[SymbolId, str],
    *,
    reserved_names: frozenset[str] = frozenset(),
) -> dict[SymbolId, str]:
    """Legalize and uniquify binder base names while preserving order."""
    result: dict[SymbolId, str] = {}
    used: set[str] = set(reserved_names)
    for sid, raw in raw_names.items():
        base = _legalize_identifier_base(raw)
        candidate = base
        suffix = 1
        while candidate in used:
            candidate = f"{base}_{suffix}"
            suffix += 1
        used.add(candidate)
        result[sid] = candidate
    return result


def _rewrite_expr(
    expr: RExpr,
    name_map: dict[SymbolId, str],
    callee_map: dict[str, str] | None,
) -> RExpr:
    def rewrite(e: RExpr) -> RExpr:
        if isinstance(e, RRef):
            new_name = name_map.get(e.symbol_id, e.name)
            if new_name != e.name:
                return RRef(symbol_id=e.symbol_id, name=new_name)
        elif isinstance(e, RModelCall) and callee_map:
            new_name = callee_map.get(e.name, e.name)
            if new_name != e.name:
                return RModelCall(name=new_name, args=e.args)
        return e

    return _map_expr(expr, rewrite)


def _rewrite_stmt(
    stmt: RStatement,
    name_map: dict[SymbolId, str],
    callee_map: dict[str, str] | None,
) -> RStatement:
    return _map_stmt(
        stmt,
        map_expr_fn=lambda e: _rewrite_expr(e, name_map, callee_map),
        map_target_name=lambda sid, name: name_map.get(sid, name),
        map_callee=((lambda c: callee_map.get(c, c)) if callee_map else None),
    )


def _collect_all_sids(func: RestrictedFunction) -> dict[SymbolId, str]:
    """Collect every ``SymbolId → raw_name`` pair from the function."""
    result: dict[SymbolId, str] = {}
    for sid, name in zip(func.params, func.param_names):
        result[sid] = name
    for sid, name in zip(func.returns, func.return_names):
        result[sid] = name

    def visit(stmt: RStatement) -> None:
        if isinstance(stmt, RAssignment):
            result[stmt.target] = stmt.target_name
        elif isinstance(stmt, RCallAssign):
            for sid, name in zip(stmt.targets, stmt.target_names):
                result[sid] = name
        elif isinstance(stmt, RConditionalBlock):
            for sid, name in zip(stmt.output_targets, stmt.output_names):
                result[sid] = name

    for_each_stmt(func.body, visit)
    return result


def _demangle_function_name(name: str) -> str:
    """Demangle a Yul function name: ``fun_f_1`` → ``f``, else identity."""
    match = re.fullmatch(r"fun_(\w+?)_\d+", name)
    return match.group(1) if match else name


@dataclass(frozen=True)
class ModuleNamePlan:
    """Module-wide naming plan before SSA versioning."""

    function_names: dict[str, str] = field(default_factory=dict)
    binder_names: dict[str, dict[SymbolId, str]] = field(default_factory=dict)


def plan_module(
    funcs: dict[str, RestrictedFunction],
    *,
    reserved_binder_names: frozenset[str] = frozenset(),
) -> ModuleNamePlan:
    """Build a complete module-wide naming plan."""
    function_names: dict[str, str] = {}
    used_fn: set[str] = set()
    for raw in funcs:
        base = _sanitize_base(_demangle_function_name(raw))
        candidate = base
        suffix = 1
        while candidate in used_fn:
            candidate = f"{base}_{suffix}"
            suffix += 1
        used_fn.add(candidate)
        function_names[raw] = candidate

    binder_names: dict[str, dict[SymbolId, str]] = {}
    for raw_name, func in funcs.items():
        binder_names[raw_name] = _uniquify_name_bases(
            _collect_all_sids(func),
            reserved_names=reserved_binder_names,
        )

    return ModuleNamePlan(
        function_names=function_names,
        binder_names=binder_names,
    )


def apply_module_plan(
    funcs: dict[str, RestrictedFunction],
    plan: ModuleNamePlan,
) -> dict[str, RestrictedFunction]:
    """Apply a ``ModuleNamePlan`` to all functions in a module."""
    result: dict[str, RestrictedFunction] = {}
    for raw_name, func in funcs.items():
        name_map = plan.binder_names.get(raw_name, {})
        function_name = plan.function_names.get(raw_name, func.name)
        result[raw_name] = RestrictedFunction(
            name=function_name,
            params=func.params,
            param_names=tuple(
                name_map.get(sid, name)
                for sid, name in zip(func.params, func.param_names)
            ),
            returns=func.returns,
            return_names=tuple(
                name_map.get(sid, name)
                for sid, name in zip(func.returns, func.return_names)
            ),
            body=tuple(
                _rewrite_stmt(stmt, name_map, plan.function_names) for stmt in func.body
            ),
        )
    return result


def next_ssa_name(
    clean: str,
    *,
    ssa_count: Counter[str],
    emitted: set[str],
) -> str:
    """Allocate the next SSA binder name for one legalized base name."""
    ssa_count[clean] += 1
    count = ssa_count[clean]
    name = clean if count == 1 else f"{clean}_{count - 1}"
    while name in emitted:
        ssa_count[clean] += 1
        count = ssa_count[clean]
        name = f"{clean}_{count - 1}"
    emitted.add(name)
    return name
