#!/usr/bin/env python3
"""
Generate Lean model of 512Math cbrt functions from Yul IR.

This script extracts `_cbrt` (512-bit, 2 params), `cbrt`/`cbrtUp` (256-bit,
1 param each), `wrap_cbrt512`, and `wrap_cbrtUp512` from the Yul IR produced
by `forge inspect` on Cbrt512Wrapper and emits opcode-faithful uint256
EVM Lean definitions (norm model suppressed via skip_norm since the proofs
bridge the EVM model directly).

The 512-bit `_cbrt` is monolithic (no sub-functions like _sqrt_babylonianStep)
so it appears as a single model. The 256-bit `cbrt`/`cbrtUp` from Cbrt.sol are
selected via `exclude_known` (leaf versions that don't call the already-targeted
512-bit `_cbrt`). The public wrappers inline all helpers as raw opcodes.

All compiler-generated helper functions (type conversions, wrapping arithmetic,
library calls) are inlined to raw opcodes automatically.
"""

from __future__ import annotations

import sys
from pathlib import Path

# Allow importing the shared module from formal/
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from yul_to_lean import ModelConfig, run

CONFIG = ModelConfig(
    function_order=(
        "_cbrt",
        # 256-bit cbrt/cbrtUp from Cbrt.sol — kept as named sub-models so the
        # public wrappers don't inline the full Newton-Raphson chain, which would
        # cause (kernel) deep recursion in the Lean proofs.
        "cbrt", "cbrtUp",
        "wrap_cbrt512", "wrap_cbrtUp512",
    ),
    model_names={
        "_cbrt": "model_cbrt512",
        "cbrt": "model_cbrt256_floor",
        "cbrtUp": "model_cbrt256_up",
        "wrap_cbrt512": "model_cbrt512_wrapper",
        "wrap_cbrtUp512": "model_cbrtUp512_wrapper",
    },
    header_comment="Auto-generated from Solidity 512Math._cbrt assembly and assignment flow.",
    generator_label="formal/cbrt/generate_cbrt512_model.py",
    extra_norm_ops={},
    extra_lean_defs="",
    norm_rewrite=None,
    inner_fn="_cbrt",
    n_params={
        "_cbrt": 2,
        "cbrt": 1,
        "cbrtUp": 1,
        "wrap_cbrt512": 2,
        "wrap_cbrtUp512": 2,
    },
    keep_solidity_locals=True,
    # 256-bit cbrt/cbrtUp share names with 512-bit wrappers; use
    # exclude_known to select the leaf (256-bit) versions that do NOT
    # call the already-targeted _cbrt (512-bit).
    exclude_known=frozenset({"cbrt", "cbrtUp"}),
    # Suppress norm models for functions whose proofs bridge the EVM model
    # directly (the norm model uses unbounded Nat which doesn't match EVM).
    skip_norm=frozenset({"cbrt", "cbrtUp", "wrap_cbrt512", "wrap_cbrtUp512"}),
    default_source_label="src/utils/512Math.sol",
    default_namespace="Cbrt512GeneratedModel",
    default_output="formal/cbrt/Cbrt512Proof/Cbrt512Proof/GeneratedCbrt512Model.lean",
    cli_description="Generate Lean model of 512Math._cbrt from Yul IR",
)


if __name__ == "__main__":
    raise SystemExit(run(CONFIG))
