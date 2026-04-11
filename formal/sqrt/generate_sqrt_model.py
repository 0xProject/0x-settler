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

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from generator_cli import run_generator
from model_config import CliConfig, EmissionConfig, ModelConfig, SelectionConfig

CONFIG = ModelConfig(
    selection=SelectionConfig(
        function_order=("_sqrt", "sqrt", "sqrtUp"),
        inner_fn="_sqrt",
    ),
    emission=EmissionConfig(
        model_names={
            "_sqrt": "model_sqrt",
            "sqrt": "model_sqrt_floor",
            "sqrtUp": "model_sqrt_up",
        },
        header_comment="Auto-generated from Solidity Sqrt assembly and assignment flow.",
        generator_label="formal/sqrt/generate_sqrt_model.py",
        norm_rewrite=None,
    ),
    cli=CliConfig(
        source_label="src/vendor/Sqrt.sol",
        namespace="SqrtGeneratedModel",
        output="formal/sqrt/SqrtProof/SqrtProof/GeneratedSqrtModel.lean",
        description="Generate Lean model of Sqrt.sol functions from Yul IR",
    ),
)


if __name__ == "__main__":
    raise SystemExit(run_generator(CONFIG))
