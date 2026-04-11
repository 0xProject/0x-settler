"""
Facade for staged Yul -> FunctionModel translation and Lean emission.

This module intentionally owns only:
- the staged translation entrypoint
- CLI glue shared by the generators
- re-exports of the live model/evaluation/emission surface
"""

from __future__ import annotations

import argparse
import pathlib
import sys

from evm_builtins import (
    BASE_NORM_HELPERS as _BASE_NORM_HELPERS,
    EVM_BUILTINS as _EVM_BUILTINS,
    OP_TO_LEAN_HELPER,
    OP_TO_OPCODE,
    WORD_MOD,
    eval_pure_builtin as _eval_builtin,
    u256,
)
from lean_emit import (
    any_norm_models,
    build_lean_source,
    build_model_body,
    emit_expr,
    render_function_defs,
)
from lean_names import validate_ident
from model_config import (
    OPTIMIZED_TRANSLATION_PIPELINE,
    UNOPTIMIZED_TRANSLATION_PIPELINE,
    ModelConfig,
    RunArguments,
    TranslationPipeline,
    TranslationResult,
)
from model_eval import build_model_table, evaluate_function_model, evaluate_model_expr
from model_helpers import (
    _expr_vars,
    collect_model_opcodes,
    collect_ops,
    collect_ops_from_statement,
)
from model_ir import (
    Assignment,
    Call,
    ConditionalBlock,
    ConditionalBranch,
    Expr,
    FunctionModel,
    Ite,
    IntLit,
    ModelStatement,
    ModelValue,
    Project,
    Var,
)
from model_transforms import (
    _prune_dead_assignments,
    apply_optional_model_transforms,
    hoist_repeated_model_calls,
)
from model_validate import validate_function_model, validate_selected_models
from yul_ast import EvaluationError as EvaluationError
from yul_ast import ParseError as ParseError
from yul_lexer import tokenize_yul


def translate_yul_to_models(
    yul_text: str,
    config: ModelConfig,
    *,
    selected_functions: tuple[str, ...] | None = None,
    pipeline: TranslationPipeline = OPTIMIZED_TRANSLATION_PIPELINE,
) -> TranslationResult:
    """Run the staged translation pipeline and return the final models."""
    from staged_pipeline import translate_selected_models

    selected = (
        selected_functions if selected_functions is not None else config.function_order
    )
    if len(set(selected)) != len(selected):
        dupes = [f for f in selected if list(selected).count(f) > 1]
        raise ParseError(f"Duplicate selected functions: {sorted(set(dupes))}")

    builtin_name_collisions = sorted(
        {name for name in selected if name in OP_TO_LEAN_HELPER}
    )
    if builtin_name_collisions:
        raise ParseError(
            "Selected function names collide with builtin model helpers: "
            f"{builtin_name_collisions}"
        )

    models = translate_selected_models(
        yul_text,
        config,
        selected_functions=selected,
    )
    validate_selected_models(models)
    models = apply_optional_model_transforms(
        models,
        config,
        pipeline=pipeline,
    )
    return TranslationResult(models=models, pipeline=pipeline)


def parse_function_selection(
    args: RunArguments,
    config: ModelConfig,
) -> tuple[str, ...]:
    selected: list[str] = []

    if args.function:
        selected.extend(args.function)
    if args.functions:
        for fn in args.functions.split(","):
            name = fn.strip()
            if name:
                selected.append(name)

    if not selected:
        selected = list(config.function_order)

    allowed = set(config.function_order)
    bad = [f for f in selected if f not in allowed]
    if bad:
        raise ParseError(f"Unsupported function(s): {', '.join(bad)}")

    if any(fn != config.inner_fn for fn in selected) and config.inner_fn not in selected:
        if config.inner_fn not in allowed:
            raise ParseError(
                f"Inner function {config.inner_fn!r} is not in function_order. "
                f"Available: {', '.join(config.function_order)}"
            )
        selected.append(config.inner_fn)

    selected_set = set(selected)
    return tuple(fn for fn in config.function_order if fn in selected_set)


def run(config: ModelConfig) -> int:
    """Main entry point shared by both generators."""
    ap = argparse.ArgumentParser(description=config.cli_description)
    ap.add_argument(
        "--yul",
        required=True,
        help="Path to Yul IR file, or '-' for stdin (from `forge inspect ... ir`)",
    )
    ap.add_argument(
        "--source-label",
        default=config.default_source_label,
        help="Source label for the Lean header comment",
    )
    ap.add_argument(
        "--functions",
        default="",
        help=f"Comma-separated function names (default: {','.join(config.function_order)})",
    )
    ap.add_argument(
        "--function",
        action="append",
        help="Optional repeatable function selector",
    )
    ap.add_argument(
        "--namespace",
        default=config.default_namespace,
        help="Lean namespace for generated definitions",
    )
    ap.add_argument(
        "--output",
        default=config.default_output,
        help="Output Lean file path",
    )
    args = ap.parse_args(namespace=RunArguments())

    validate_ident(args.namespace, what="Lean namespace")

    selected_functions = parse_function_selection(args, config)
    pipeline = OPTIMIZED_TRANSLATION_PIPELINE

    if args.yul == "-":
        stdin = sys.stdin
        if stdin is None:
            raise ParseError("stdin is unavailable while reading Yul input")
        yul_text = stdin.read()
    else:
        yul_text = pathlib.Path(args.yul).read_text()

    result = translate_yul_to_models(
        yul_text,
        config,
        selected_functions=selected_functions,
        pipeline=pipeline,
    )
    models = result.models

    lean_src = build_lean_source(
        models=models,
        source_path=args.source_label,
        namespace=args.namespace,
        config=config,
    )

    out_path = pathlib.Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(lean_src)

    print(f"Generated {out_path}")
    for model in models:
        print(f"Parsed {len(model.assignments)} assignments for {model.fn_name}")

    opcodes = collect_model_opcodes(models)
    print(f"Modeled opcodes: {', '.join(opcodes)}")

    return 0
