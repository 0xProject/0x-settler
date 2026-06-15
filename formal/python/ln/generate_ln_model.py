#!/usr/bin/env python3
"""
Generate Lean models of Ln.sol from Yul IR.

This script extracts `lnWadToRay` and `lnWad` from the Yul IR produced by
`forge inspect` on a wrapper contract and emits Lean definitions with
opcode-faithful uint256 EVM semantics.

The non-positive-input revert guard (a `Panic(uint256)` with the
division-by-zero code `0x12`) is stripped before translation: the memory
model only supports straight-line memory writes, and every Lean theorem
about the model quantifies over the non-reverting domain 0 < x < 2**255
anyway. The strip is exact-match and fails loudly if the guard's shape in
the IR ever changes.
"""

from __future__ import annotations

import re
from typing import cast

_REVERT_GUARD = re.compile(
    r"if\s+iszero\(slt\(0x00,\s*(\w+)\)\)\s*"
    r"\{\s*mstore\(0x00,\s*0x4e487b71\)\s*mstore\(0x20,\s*0x12\)\s*"
    r"revert\(0x1c,\s*0x24\)\s*\}",
)


def strip_revert_guard(yul_text: str) -> str:
    stripped, count = _REVERT_GUARD.subn("", yul_text)
    if count != 1:
        raise SystemExit(
            "expected exactly one non-positive-input revert guard in the Yul"
            f" IR, found {count}"
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
        function_order=("lnWadToRay", "lnWad"),
        inner_fn="lnWadToRay",
    ),
    emission=EmissionConfig(
        # The model identifiers keep their established names: `model_ln_wad` is the
        # ray-output computation (Solidity `lnWadToRay`) and `model_ln_wad_to_wad` is
        # the wad-output computation (Solidity `lnWad`), matching every theorem in the
        # proof corpus.
        model_names={
            "lnWadToRay": "model_ln_wad",
            "lnWad": "model_ln_wad_to_wad",
        },
        header_comment="Auto-generated from Solidity Ln assembly and assignment flow.",
        generator_label="formal/python/ln/generate_ln_model.py",
        norm_rewrite=None,
    ),
    transforms=TransformConfig(
        skip_norm=frozenset({"lnWadToRay", "lnWad"}),
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
        # typeshed types `sys.stdin` as `TextIO | Any`; the read is a `str`.
        yul_text = cast(str, sys.stdin.read())
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
