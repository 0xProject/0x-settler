from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field

from model_ir import Expr


@dataclass(frozen=True)
class SelectionConfig:
    function_order: tuple[str, ...]
    inner_fn: str
    n_params: dict[str, int] = field(default_factory=dict)
    exact_yul_names: dict[str, str] = field(default_factory=dict)
    require_reaching_selected: dict[str, frozenset[str]] = field(default_factory=dict)
    avoid_reaching_selected: dict[str, frozenset[str]] = field(default_factory=dict)


@dataclass(frozen=True)
class TransformConfig:
    skip_norm: frozenset[str] = frozenset()
    hoist_repeated_calls: frozenset[str] = frozenset()
    skip_prune: frozenset[str] = frozenset()


@dataclass(frozen=True)
class NormExtension:
    op_name: str
    lean_name: str
    lean_def: str


@dataclass(frozen=True)
class EmissionConfig:
    model_names: dict[str, str]
    header_comment: str
    generator_label: str
    norm_rewrite: Callable[[Expr], Expr] | None
    norm_extensions: tuple[NormExtension, ...] = ()

    def norm_helper_map(self) -> dict[str, str]:
        return {
            extension.op_name: extension.lean_name for extension in self.norm_extensions
        }

    def norm_helper_names(self) -> frozenset[str]:
        return frozenset(extension.lean_name for extension in self.norm_extensions)


@dataclass(frozen=True)
class CliConfig:
    source_label: str = ""
    namespace: str = ""
    output: str = ""
    description: str = ""


@dataclass(frozen=True)
class ModelConfig:
    selection: SelectionConfig
    emission: EmissionConfig
    transforms: TransformConfig = field(default_factory=TransformConfig)
    cli: CliConfig = field(default_factory=CliConfig)
