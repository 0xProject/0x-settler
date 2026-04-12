from __future__ import annotations

import types
from collections.abc import Callable, Mapping
from dataclasses import dataclass, field

from .model_ir import Expr


def _freeze_mapping(
    values: Mapping[str, object],
) -> types.MappingProxyType[str, object]:
    return types.MappingProxyType(dict(values))


def _freeze_frozenset_mapping(
    values: Mapping[str, frozenset[str]],
) -> types.MappingProxyType[str, frozenset[str]]:
    return types.MappingProxyType(dict(values))


@dataclass(frozen=True)
class SelectionConfig:
    function_order: tuple[str, ...]
    inner_fn: str
    n_params: Mapping[str, int] = field(default_factory=dict)
    exact_yul_names: Mapping[str, str] = field(default_factory=dict)
    require_reaching_selected: Mapping[str, frozenset[str]] = field(
        default_factory=dict
    )
    avoid_reaching_selected: Mapping[str, frozenset[str]] = field(default_factory=dict)

    def __post_init__(self) -> None:
        function_order: tuple[str, ...] = tuple(self.function_order)
        n_params = _freeze_mapping(self.n_params)
        exact_yul_names = _freeze_mapping(self.exact_yul_names)
        require_reaching_selected = _freeze_frozenset_mapping(
            self.require_reaching_selected
        )
        avoid_reaching_selected = _freeze_frozenset_mapping(
            self.avoid_reaching_selected
        )

        object.__setattr__(self, "function_order", function_order)
        object.__setattr__(self, "n_params", n_params)
        object.__setattr__(
            self,
            "exact_yul_names",
            exact_yul_names,
        )
        object.__setattr__(
            self,
            "require_reaching_selected",
            require_reaching_selected,
        )
        object.__setattr__(
            self,
            "avoid_reaching_selected",
            avoid_reaching_selected,
        )


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
    """Backend-facing emission settings.

    ``norm_rewrite``, when set, is a local expression rewrite applied bottom-up
    to every model-expression node before normalized Lean emission. The hook
    receives one node whose children have already been rewritten and returns the
    replacement for that node.
    """

    model_names: Mapping[str, str]
    header_comment: str
    generator_label: str
    norm_rewrite: Callable[[Expr], Expr] | None
    norm_extensions: tuple[NormExtension, ...] = ()

    def __post_init__(self) -> None:
        model_names = _freeze_mapping(self.model_names)
        norm_extensions: tuple[NormExtension, ...] = tuple(self.norm_extensions)

        object.__setattr__(self, "model_names", model_names)
        object.__setattr__(self, "norm_extensions", norm_extensions)

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
