"""
Library entrypoint for Yul -> FunctionModel translation.
"""

from __future__ import annotations

from model_config import ModelConfig
from model_transforms import apply_optional_model_transforms
from model_validate import validate_model_set
from staged_pipeline import translate_selected_models
from staged_selection import build_selection_plan, normalize_requested_functions


def translate_yul_to_models(
    yul_text: str,
    config: ModelConfig,
    *,
    selected_functions: tuple[str, ...] | None = None,
    optimize: bool = True,
) -> list["FunctionModel"]:
    selected = normalize_requested_functions(config.selection, selected_functions)
    selection_plan = build_selection_plan(
        yul_text,
        config.selection,
        selected_functions=selected,
    )
    models = translate_selected_models(selection_plan)
    models = apply_optional_model_transforms(
        models,
        config.transforms,
        model_call_names=frozenset(config.selection.function_order),
        optimize=optimize,
    )
    validate_model_set(models)
    return models


from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from model_ir import FunctionModel
