#!/usr/bin/env python3
"""
Generate Lean models of Cbrt.sol from Yul IR.

This script extracts `_cbrt`, `cbrt`, and `cbrtUp` from the Yul IR produced by
`forge inspect` on a wrapper contract and emits Lean definitions for:
- opcode-faithful uint256 EVM semantics, and
- normalized Nat semantics.
"""

from __future__ import annotations

if __package__ in (None, ""):
    import pathlib
    import sys

    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[3]))

    from formal.python.generator_cli import run_generator
    from formal.python.model_config import (
        CliConfig,
        EmissionConfig,
        ModelConfig,
        SelectionConfig,
    )
else:
    from ..generator_cli import run_generator
    from ..model_config import (
        CliConfig,
        EmissionConfig,
        ModelConfig,
        SelectionConfig,
    )


CONFIG = ModelConfig(
    selection=SelectionConfig(
        function_order=("_cbrt", "cbrt", "cbrtUp"),
        inner_fn="_cbrt",
    ),
    emission=EmissionConfig(
        model_names={
            "_cbrt": "model_cbrt",
            "cbrt": "model_cbrt_floor",
            "cbrtUp": "model_cbrt_up",
        },
        header_comment="Auto-generated from Solidity Cbrt assembly and assignment flow.",
        generator_label="formal/python/cbrt/generate_cbrt_model.py",
        norm_rewrite=None,
    ),
    cli=CliConfig(
        source_label="src/vendor/Cbrt.sol",
        namespace="CbrtGeneratedModel",
        output="formal/cbrt/CbrtProof/CbrtProof/GeneratedCbrtModel.lean",
        description="Generate Lean model of Cbrt.sol functions from Yul IR",
    ),
)


if __name__ == "__main__":
    raise SystemExit(run_generator(CONFIG))
