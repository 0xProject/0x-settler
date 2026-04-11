from __future__ import annotations

import argparse
import pathlib
import sys
from typing import cast

from lean_emit import build_lean_source
from lean_names import validate_ident
from model_config import ModelConfig
from model_helpers import collect_model_opcodes
from staged_selection import normalize_requested_functions

from yul_ast import ParseError
from yul_to_lean import translate_yul_to_models


class _CliArgs(argparse.Namespace):
    yul: str
    source_label: str
    functions: str
    function: list[str] | None
    namespace: str
    output: str


def run_generator(config: ModelConfig) -> int:
    parser = argparse.ArgumentParser(description=config.cli.description)
    parser.add_argument(
        "--yul",
        required=True,
        help="Path to Yul IR file, or '-' for stdin (from `forge inspect ... ir`)",
    )
    parser.add_argument(
        "--source-label",
        default=config.cli.source_label,
        help="Source label for the Lean header comment",
    )
    parser.add_argument(
        "--functions",
        default="",
        help=(
            "Comma-separated function names "
            f"(default: {','.join(config.selection.function_order)})"
        ),
    )
    parser.add_argument(
        "--function",
        action="append",
        help="Optional repeatable function selector",
    )
    parser.add_argument(
        "--namespace",
        default=config.cli.namespace,
        help="Lean namespace for generated definitions",
    )
    parser.add_argument(
        "--output",
        default=config.cli.output,
        help="Output Lean file path",
    )
    args = parser.parse_args(namespace=_CliArgs())

    validate_ident(args.namespace, what="Lean namespace")
    selected_functions = _parse_function_selection(
        config, args.function, args.functions
    )
    if args.yul == "-":
        stdin = sys.stdin
        if stdin is None:
            raise ParseError("stdin is unavailable while reading Yul input")
        yul_text = cast(str, stdin.read())
    else:
        yul_text = pathlib.Path(args.yul).read_text()

    models = translate_yul_to_models(
        yul_text,
        config,
        selected_functions=selected_functions,
    )
    lean_src = build_lean_source(
        models=models,
        source_path=args.source_label,
        namespace=args.namespace,
        emission=config.emission,
        transforms=config.transforms,
    )

    out_path = pathlib.Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(lean_src)

    print(f"Generated {out_path}")
    for model in models:
        print(f"Parsed {len(model.assignments)} assignments for {model.fn_name}")
    print(f"Modeled opcodes: {', '.join(collect_model_opcodes(models))}")
    return 0


def _parse_function_selection(
    config: ModelConfig,
    functions: list[str] | None,
    csv_functions: str,
) -> tuple[str, ...]:
    selected: list[str] = []
    if functions:
        selected.extend(functions)
    for raw_name in csv_functions.split(","):
        name = raw_name.strip()
        if name:
            selected.append(name)
    return normalize_requested_functions(
        config.selection,
        selected or None,
    )
