#!/usr/bin/env python3
from __future__ import annotations

from decimal import Decimal, localcontext

from formal.python.evm_builtins import WORD_MOD, eval_pure_builtin, u256

WAD = 10**18
SIGN_BIT = 1 << 255

# x = WAD + 1 is the witness input for the floor specification: the exact result lies
# strictly between 0 and 1, so any rounding mode other than floor (or floor - 1) is
# detectable here.
WITNESS_X = WAD + 1
EXPECTED_FLOOR_RESULT = 0

# Constants mirrored from src/vendor/Ln.sol (see the comments there for derivations).
_S = 0x16A09E667F3BCC908B2FB1367
_P3 = 0x35DF006E603CD672CC56856F
_P2 = 0x4D2343BBE6F1BC6BC52C19476
_P1 = 0xF7EB3D8E052BCBF7EE1828049
_P0 = 0xC0631C0B347DE96C2C5867380
_Q2 = 0x8EAD228F38FE4D674CA1BF0B2
_Q1 = 0x1380C46E716AAF05B93B36E930
_Q0 = 0xC0631C0B347DE968FAD1273F4
_C = 0x6F05B59D3B2
_LN2 = 0x267A36C0C95B3975AB3EE5B203A7614A3F7
_BIAS = 0x58452FFD07D74B4395BF265EA3C4E3C7F3F1


def _op(name: str, *args: int) -> int:
    return eval_pure_builtin(name, tuple(args))


def _i256(word: int) -> int:
    word = u256(word)
    return word - WORD_MOD if word >= SIGN_BIT else word


def ln_wad_evm(x: int) -> int:
    """Step-for-step mirror of `Ln.lnWad` from src/vendor/Ln.sol."""
    x_word = u256(x)
    if _op("iszero", _op("sgt", x_word, 0)) != 0:
        raise ValueError("LnWadUndefined")

    c = _op("clz", x_word)
    k = _op("sub", 0x9F, c)
    x_word = _op("shr", 0x9F, _op("shl", c, x_word))

    z = _op("sdiv", _op("shl", 0x60, _op("sub", x_word, _S)), _op("add", x_word, _S))
    u = _op("shr", 0x60, _op("mul", z, z))

    p = _op("sub", _op("sar", 0x60, _op("mul", _P3, u)), _P2)
    p = _op("add", _op("sar", 0x60, _op("mul", p, u)), _P1)
    p = _op("sub", _op("sar", 0x60, _op("mul", p, u)), _P0)

    q = _op("sub", u, _Q2)
    q = _op("add", _op("sar", 0x60, _op("mul", q, u)), _Q1)
    q = _op("sub", _op("sar", 0x60, _op("mul", q, u)), _Q0)

    r = _op("sdiv", _op("mul", _C, _op("mul", p, z)), q)
    r = _op("add", r, _op("mul", _LN2, k))
    r = _op("add", r, _BIAS)
    return _i256(_op("sar", 0x4E, r))


def floor_spec_for_witness(x: int) -> int:
    if x != WAD + 1:
        raise ValueError("exact floor proof is specialized to WAD + 1")

    # For t > 0, 0 < ln(1 + t) < t. With t = 1 / WAD, the exact value
    # WAD * ln(1 + t) is strictly between 0 and 1, so its floor is 0.
    return 0


def decimal_ln_wad(x: int) -> Decimal:
    with localcontext() as ctx:
        ctx.prec = 120
        return (Decimal(x) / Decimal(WAD)).ln() * Decimal(WAD)


def main() -> int:
    actual = ln_wad_evm(WITNESS_X)
    expected = floor_spec_for_witness(WITNESS_X)
    value = decimal_ln_wad(WITNESS_X)

    assert expected == EXPECTED_FLOOR_RESULT, expected
    # lnWad must return floor(L) or floor(L) - 1.
    assert actual in (expected, expected - 1), actual
    # lnWad(WAD) likewise: floor(L) = 0, so the result must be 0 or -1.
    assert ln_wad_evm(WAD) in (0, -1)

    print(f"x = {WITNESS_X}")
    print(f"lnWad EVM result = {actual}")
    print(f"floor mathematical result = {expected}")
    print(f"1e18 * ln(x / 1e18) = {value}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
