#!/usr/bin/env python3
"""
Generate Lean model of 512Math._sqrt from Yul IR.

This script extracts `_innerSqrt`, `_karatsubaQuotient`, `_sqrtCorrection`,
and `_sqrt` from the Yul IR produced by `forge inspect` on Sqrt512Wrapper
and emits Lean definitions for:
- opcode-faithful uint256 EVM semantics, and
- normalized Nat semantics.

By keeping all four functions in `function_order`, the pipeline emits
separate models for each sub-function. `model_sqrt512_evm` calls into
`model_innerSqrt_evm`, `model_karatsubaQuotient_evm`, and
`model_sqrtCorrection_evm` rather than inlining their bodies, producing
smaller Lean terms that are easier to prove correct individually.

All compiler-generated helper functions (type conversions, wrapping
arithmetic, library calls) are inlined to raw opcodes automatically.
"""

from __future__ import annotations

import sys
from pathlib import Path

# Allow importing the shared module from formal/
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from yul_to_lean import ModelConfig, run

CONFIG = ModelConfig(
    function_order=("_bstep", "_innerSqrt", "_karatsubaQuotient", "_sqrtCorrection", "_sqrt"),
    model_names={
        "_bstep": "model_bstep",
        "_innerSqrt": "model_innerSqrt",
        "_karatsubaQuotient": "model_karatsubaQuotient",
        "_sqrtCorrection": "model_sqrtCorrection",
        "_sqrt": "model_sqrt512",
    },
    header_comment="Auto-generated from Solidity 512Math._sqrt assembly and assignment flow.",
    generator_label="formal/sqrt/generate_sqrt512_model.py",
    extra_norm_ops={},
    extra_lean_defs="",
    norm_rewrite=None,
    inner_fn="_sqrt",
    n_params={
        "_bstep": 2,
        "_innerSqrt": 1,
        "_karatsubaQuotient": 3,
        "_sqrtCorrection": 4,
        "_sqrt": 2,
    },
    keep_solidity_locals=True,
    default_source_label="src/utils/512Math.sol",
    default_namespace="Sqrt512GeneratedModel",
    default_output="formal/sqrt/Sqrt512Proof/Sqrt512Proof/GeneratedSqrt512Model.lean",
    cli_description="Generate Lean model of 512Math._sqrt from Yul IR",
)


if __name__ == "__main__":
    raise SystemExit(run(CONFIG))
