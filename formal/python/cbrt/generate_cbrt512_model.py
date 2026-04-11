#!/usr/bin/env python3
"""
Generate Lean model of 512Math cbrt functions from Yul IR.

This script extracts the cbrt sub-functions and wrappers from the Yul IR
produced by `forge inspect` on Cbrt512Wrapper and emits opcode-faithful
uint256 EVM Lean definitions.  Only the EVM-faithful (`_evm`) models are
generated; the unbounded-Nat norm models are suppressed because the 512-bit
proofs bridge the EVM model directly.

Sub-functions (listed before `_cbrt` so they're emitted as named sub-models):
  _cbrt_newtonRaphsonStep  — one Newton-Raphson step (2 params)
  _cbrt_baseCase           — seed + 6 NR + floor correction (1 param → 3 returns)
  _cbrt_karatsubaQuotient  — Karatsuba division step (3 params)
  _cbrt_quadraticCorrection — quadratic correction + recombine (3 params)
  _cbrt                    — normalize + sub-function calls + un-normalize (2 params)

The 256-bit `cbrt`/`cbrtUp` from Cbrt.sol are selected by requiring them not
to reach the selected 512-bit `_cbrt`.
The public wrappers call the named `_cbrt` / 256-bit sub-models and inline the
remaining compiler-generated helpers to raw opcodes.

All compiler-generated helper functions (type conversions, wrapping arithmetic,
library calls) are inlined to raw opcodes automatically.
"""

from __future__ import annotations

from ..generator_cli import run_generator
from ..model_config import (
    CliConfig,
    EmissionConfig,
    ModelConfig,
    SelectionConfig,
    TransformConfig,
)

CONFIG = ModelConfig(
    selection=SelectionConfig(
        function_order=(
            "_cbrt_newtonRaphsonStep",
            "_cbrt_baseCase",
            "_cbrt_karatsubaQuotient",
            "_cbrt_quadraticCorrection",
            "_cbrt",
            "cbrt",
            "cbrtUp",
            "wrap_cbrt512",
            "wrap_cbrtUp512",
        ),
        inner_fn="_cbrt",
        n_params={
            "_cbrt_newtonRaphsonStep": 2,
            "_cbrt_baseCase": 1,
            "_cbrt_karatsubaQuotient": 3,
            "_cbrt_quadraticCorrection": 3,
            "_cbrt": 2,
            "cbrt": 1,
            "cbrtUp": 1,
            "wrap_cbrt512": 2,
            "wrap_cbrtUp512": 2,
        },
        avoid_reaching_selected={
            "cbrt": frozenset({"_cbrt"}),
            "cbrtUp": frozenset({"_cbrt"}),
        },
    ),
    emission=EmissionConfig(
        model_names={
            "_cbrt_newtonRaphsonStep": "model_cbrtNRStep",
            "_cbrt_baseCase": "model_cbrtBaseCase",
            "_cbrt_karatsubaQuotient": "model_cbrtKaratsubaQuotient",
            "_cbrt_quadraticCorrection": "model_cbrtQuadraticCorrection",
            "_cbrt": "model_cbrt512",
            "cbrt": "model_cbrt256_floor",
            "cbrtUp": "model_cbrt256_up",
            "wrap_cbrt512": "model_cbrt512_wrapper",
            "wrap_cbrtUp512": "model_cbrtUp512_wrapper",
        },
        header_comment="Auto-generated from Solidity 512Math._cbrt assembly and assignment flow.",
        generator_label="formal/python/cbrt/generate_cbrt512_model.py",
        norm_rewrite=None,
    ),
    transforms=TransformConfig(
        skip_norm=frozenset(
            {
                "_cbrt_newtonRaphsonStep",
                "_cbrt_baseCase",
                "_cbrt_karatsubaQuotient",
                "_cbrt_quadraticCorrection",
                "_cbrt",
                "cbrt",
                "cbrtUp",
                "wrap_cbrt512",
                "wrap_cbrtUp512",
            }
        ),
        hoist_repeated_calls=frozenset({"wrap_cbrt512", "wrap_cbrtUp512"}),
    ),
    cli=CliConfig(
        source_label="src/utils/512Math.sol",
        namespace="Cbrt512GeneratedModel",
        output="formal/cbrt/Cbrt512Proof/Cbrt512Proof/GeneratedCbrt512Model.lean",
        description="Generate Lean model of 512Math._cbrt from Yul IR",
    ),
)


if __name__ == "__main__":
    raise SystemExit(run_generator(CONFIG))
