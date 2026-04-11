#!/usr/bin/env python3
"""
Generate Lean models of Cbrt.sol from Yul IR.

This script extracts `_cbrt`, `cbrt`, and `cbrtUp` from the Yul IR produced by
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
from model_ir import Call, Expr, IntLit

from yul_to_lean import run


def rewrite_norm_ast(expr: Expr) -> Expr:
    """Rewrite sub(257, clz(arg)) → bitLengthPlus1(arg) for the Nat model.

    In Nat arithmetic, normSub 257 (normClz x) = 257 - (255 - log2 x) underflows
    for x ≥ 2^256 because 255 - log2 x truncates to 0.  normBitLengthPlus1(x)
    computes log2(x) + 2 directly, giving the correct value for all Nat.
    """
    if isinstance(expr, Call):
        args = tuple(rewrite_norm_ast(a) for a in expr.args)
        if (
            expr.name == "sub"
            and len(args) == 2
            and isinstance(args[0], IntLit)
            and args[0].value == 257
            and isinstance(args[1], Call)
            and args[1].name == "clz"
            and len(args[1].args) == 1
        ):
            return Call("bitLengthPlus1", args[1].args)
        return Call(expr.name, args)
    return expr


CONFIG = ModelConfig(
    function_order=("_cbrt", "cbrt", "cbrtUp"),
    model_names={
        "_cbrt": "model_cbrt",
        "cbrt": "model_cbrt_floor",
        "cbrtUp": "model_cbrt_up",
    },
    header_comment="Auto-generated from Solidity Cbrt assembly and assignment flow.",
    generator_label="formal/cbrt/generate_cbrt_model.py",
    extra_norm_ops={"bitLengthPlus1": "normBitLengthPlus1"},
    extra_lean_defs=(
        "def normBitLengthPlus1 (value : Nat) : Nat :=\n"
        "  if value = 0 then 1 else Nat.log2 value + 2\n\n"
    ),
    norm_rewrite=rewrite_norm_ast,
    inner_fn="_cbrt",
    default_source_label="src/vendor/Cbrt.sol",
    default_namespace="CbrtGeneratedModel",
    default_output="formal/cbrt/CbrtProof/CbrtProof/GeneratedCbrtModel.lean",
    cli_description="Generate Lean model of Cbrt.sol functions from Yul IR",
)


if __name__ == "__main__":
    raise SystemExit(run(CONFIG))
