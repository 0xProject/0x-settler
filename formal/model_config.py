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


@dataclass(frozen=True, init=False)
class ModelConfig:
    selection: SelectionConfig
    emission: EmissionConfig
    transforms: TransformConfig = field(default_factory=TransformConfig)
    cli: CliConfig = field(default_factory=CliConfig)

    def __init__(
        self,
        selection: SelectionConfig | None = None,
        emission: EmissionConfig | None = None,
        transforms: TransformConfig | None = None,
        cli: CliConfig | None = None,
        *,
        function_order: tuple[str, ...] | None = None,
        model_names: dict[str, str] | None = None,
        header_comment: str | None = None,
        generator_label: str | None = None,
        extra_norm_ops: dict[str, str] | None = None,
        extra_lean_defs: str | None = None,
        norm_rewrite: Callable[[Expr], Expr] | None = None,
        inner_fn: str | None = None,
        n_params: dict[str, int] | None = None,
        exact_yul_names: dict[str, str] | None = None,
        require_reaching_selected: dict[str, frozenset[str]] | None = None,
        avoid_reaching_selected: dict[str, frozenset[str]] | None = None,
        skip_norm: frozenset[str] = frozenset(),
        hoist_repeated_calls: frozenset[str] = frozenset(),
        skip_prune: frozenset[str] = frozenset(),
        default_source_label: str = "",
        default_namespace: str = "",
        default_output: str = "",
        cli_description: str = "",
    ) -> None:
        using_nested = any(
            part is not None for part in (selection, emission, transforms, cli)
        )
        if using_nested:
            if selection is None or emission is None:
                raise TypeError("ModelConfig requires selection and emission")
            object.__setattr__(self, "selection", selection)
            object.__setattr__(self, "emission", emission)
            object.__setattr__(self, "transforms", transforms or TransformConfig())
            object.__setattr__(self, "cli", cli or CliConfig())
            return

        if function_order is None or model_names is None:
            raise TypeError(
                "Flat ModelConfig construction requires function_order and model_names"
            )

        extensions = _flat_norm_extensions(extra_norm_ops or {}, extra_lean_defs or "")
        object.__setattr__(
            self,
            "selection",
            SelectionConfig(
                function_order=function_order,
                inner_fn=inner_fn or function_order[0],
                n_params=n_params or {},
                exact_yul_names=exact_yul_names or {},
                require_reaching_selected=require_reaching_selected or {},
                avoid_reaching_selected=avoid_reaching_selected or {},
            ),
        )
        object.__setattr__(
            self,
            "emission",
            EmissionConfig(
                model_names=model_names,
                header_comment=header_comment or "",
                generator_label=generator_label or "",
                norm_rewrite=norm_rewrite,
                norm_extensions=extensions,
            ),
        )
        object.__setattr__(
            self,
            "transforms",
            TransformConfig(
                skip_norm=skip_norm,
                hoist_repeated_calls=hoist_repeated_calls,
                skip_prune=skip_prune,
            ),
        )
        object.__setattr__(
            self,
            "cli",
            CliConfig(
                source_label=default_source_label,
                namespace=default_namespace,
                output=default_output,
                description=cli_description,
            ),
        )

    @property
    def function_order(self) -> tuple[str, ...]:
        return self.selection.function_order

    @property
    def inner_fn(self) -> str:
        return self.selection.inner_fn

    @property
    def n_params(self) -> dict[str, int]:
        return self.selection.n_params

    @property
    def exact_yul_names(self) -> dict[str, str]:
        return self.selection.exact_yul_names

    @property
    def require_reaching_selected(self) -> dict[str, frozenset[str]]:
        return self.selection.require_reaching_selected

    @property
    def model_names(self) -> dict[str, str]:
        return self.emission.model_names

    @property
    def header_comment(self) -> str:
        return self.emission.header_comment

    @property
    def generator_label(self) -> str:
        return self.emission.generator_label

    @property
    def norm_rewrite(self) -> Callable[[Expr], Expr] | None:
        return self.emission.norm_rewrite

    @property
    def extra_norm_ops(self) -> dict[str, str]:
        return self.emission.norm_helper_map()

    @property
    def extra_lean_defs(self) -> str:
        return "\n\n".join(
            extension.lean_def.rstrip()
            for extension in self.emission.norm_extensions
            if extension.lean_def.strip()
        )

    @property
    def skip_norm(self) -> frozenset[str]:
        return self.transforms.skip_norm

    @property
    def hoist_repeated_calls(self) -> frozenset[str]:
        return self.transforms.hoist_repeated_calls

    @property
    def skip_prune(self) -> frozenset[str]:
        return self.transforms.skip_prune

    @property
    def default_source_label(self) -> str:
        return self.cli.source_label

    @property
    def default_namespace(self) -> str:
        return self.cli.namespace

    @property
    def default_output(self) -> str:
        return self.cli.output

    @property
    def cli_description(self) -> str:
        return self.cli.description


def _flat_norm_extensions(
    extra_norm_ops: dict[str, str],
    extra_lean_defs: str,
) -> tuple[NormExtension, ...]:
    if not extra_norm_ops:
        return ()
    stripped = extra_lean_defs.strip()
    if len(extra_norm_ops) != 1 or not stripped:
        raise TypeError(
            "Flat ModelConfig construction only supports a single norm extension. "
            "Use EmissionConfig.norm_extensions for the structured form."
        )
    op_name, lean_name = next(iter(extra_norm_ops.items()))
    return (
        NormExtension(
            op_name=op_name,
            lean_name=lean_name,
            lean_def=stripped,
        ),
    )
