#!/usr/bin/env python3
"""
Generate Lean models of Ln.sol from Yul IR.

This script extracts `lnWad` and `lnWadToWad` from the Yul IR produced by
`forge inspect` on a wrapper contract and emits Lean definitions with
opcode-faithful uint256 EVM semantics.

The `LnWadUndefined()` revert guard is stripped before translation: the
memory model only supports straight-line memory writes, and every Lean
theorem about the model quantifies over the non-reverting domain
0 < x < 2**255 anyway. The strip is exact-match and fails loudly if the
guard's shape in the IR ever changes.
"""

from __future__ import annotations

import re

_REVERT_GUARD = re.compile(
    r"if\s+iszero\(sgt\((\w+),\s*0\)\)\s*"
    r"\{\s*mstore\(0x00,\s*0x1615e638\)\s*revert\(0x1c,\s*0x04\)\s*\}",
)


def strip_revert_guard(yul_text: str) -> str:
    stripped, count = _REVERT_GUARD.subn("", yul_text)
    if count != 1:
        raise SystemExit(
            f"expected exactly one LnWadUndefined() revert guard in the Yul IR, found {count}"
        )
    return stripped

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
        TransformConfig,
    )
else:
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
        function_order=("lnWad", "lnWadToWad"),
        inner_fn="lnWad",
    ),
    emission=EmissionConfig(
        model_names={
            "lnWad": "model_ln_wad",
            "lnWadToWad": "model_ln_wad_to_wad",
        },
        header_comment="Auto-generated from Solidity Ln assembly and assignment flow.",
        generator_label="formal/python/ln/generate_ln_model.py",
        norm_rewrite=None,
    ),
    transforms=TransformConfig(
        skip_norm=frozenset({"lnWad", "lnWadToWad"}),
    ),
    cli=CliConfig(
        source_label="src/vendor/Ln.sol",
        namespace="LnGeneratedModel",
        output="formal/ln/LnProof/LnProof/GeneratedLnModel.lean",
        description="Generate Lean model of Ln.sol functions from Yul IR",
    ),
)


def main() -> int:
    import sys
    import tempfile

    argv = sys.argv[1:]
    try:
        yul_at = argv.index("--yul")
        yul_arg = argv[yul_at + 1]
    except (ValueError, IndexError):
        raise SystemExit("--yul <path|-> is required")

    if yul_arg == "-":
        yul_text = sys.stdin.read()
    else:
        with open(yul_arg) as source:
            yul_text = source.read()
    with tempfile.NamedTemporaryFile("w", suffix=".yul", delete=False) as handle:
        handle.write(strip_revert_guard(yul_text))
        argv[yul_at + 1] = handle.name
    sys.argv[1:] = argv
    return run_generator(CONFIG)


if __name__ == "__main__":
    raise SystemExit(main())
