#!/usr/bin/env python3
"""
Generate Lean models of Sqrt.sol from Yul IR.

This script extracts `_sqrt`, `sqrt`, and `sqrtUp` from the Yul IR produced by
`forge inspect` on a wrapper contract and emits Lean definitions for:
- opcode-faithful uint256 EVM semantics, and
- normalized Nat semantics.
"""

from __future__ import annotations

import sys
from pathlib import Path

# Allow importing the shared module from formal/
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from model_config import ModelConfig
from yul_to_lean import run

CONFIG = ModelConfig(
    function_order=("_sqrt", "sqrt", "sqrtUp"),
    model_names={
        "_sqrt": "model_sqrt",
        "sqrt": "model_sqrt_floor",
        "sqrtUp": "model_sqrt_up",
    },
    header_comment="Auto-generated from Solidity Sqrt assembly and assignment flow.",
    generator_label="formal/sqrt/generate_sqrt_model.py",
    extra_norm_ops={},
    extra_lean_defs="",
    norm_rewrite=None,
    inner_fn="_sqrt",
    default_source_label="src/vendor/Sqrt.sol",
    default_namespace="SqrtGeneratedModel",
    default_output="formal/sqrt/SqrtProof/SqrtProof/GeneratedSqrtModel.lean",
    cli_description="Generate Lean model of Sqrt.sol functions from Yul IR",
)


if __name__ == "__main__":
    raise SystemExit(run(CONFIG))
