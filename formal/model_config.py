from __future__ import annotations

import argparse
from dataclasses import dataclass
from typing import Callable

from model_ir import Expr, FunctionModel


@dataclass(frozen=True)
class TranslationPipeline:
    """Controls optional post-processing passes on staged `FunctionModel`s."""

    name: str
    hoist_repeated_calls: bool
    prune_dead_assignments: bool


UNOPTIMIZED_TRANSLATION_PIPELINE = TranslationPipeline(
    name="unoptimized",
    hoist_repeated_calls=False,
    prune_dead_assignments=False,
)

OPTIMIZED_TRANSLATION_PIPELINE = TranslationPipeline(
    name="optimized",
    # Zero-assignment elision is not semantics-preserving in general. Keep the
    # optimized default limited to passes with direct equivalence tests.
    hoist_repeated_calls=True,
    prune_dead_assignments=True,
)

# Backward-compatible alias kept only because older tests and callers still
# spell this pipeline "raw" even though translation now always uses the staged
# path and this flag only controls optional post-processing.
RAW_TRANSLATION_PIPELINE = UNOPTIMIZED_TRANSLATION_PIPELINE


@dataclass(frozen=True)
class ModelConfig:
    """All the per-library knobs that differ between cbrt and sqrt generators."""

    function_order: tuple[str, ...]
    model_names: dict[str, str]
    header_comment: str
    generator_label: str
    extra_norm_ops: dict[str, str]
    extra_lean_defs: str
    norm_rewrite: Callable[[Expr], Expr] | None
    inner_fn: str
    n_params: dict[str, int] | None = None
    exact_yul_names: dict[str, str] | None = None
    keep_solidity_locals: bool = False
    exclude_known: frozenset[str] = frozenset()
    skip_norm: frozenset[str] = frozenset()
    hoist_repeated_calls: frozenset[str] = frozenset()
    skip_prune: frozenset[str] = frozenset()

    default_source_label: str = ""
    default_namespace: str = ""
    default_output: str = ""
    cli_description: str = ""


@dataclass(frozen=True)
class TranslationResult:
    """End-to-end translation result before Lean source emission."""

    models: list[FunctionModel]
    pipeline: TranslationPipeline


class RunArguments(argparse.Namespace):
    yul: str
    source_label: str
    functions: str
    function: list[str] | None
    namespace: str
    output: str
