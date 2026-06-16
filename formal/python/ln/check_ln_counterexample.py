#!/usr/bin/env python3
from __future__ import annotations

from decimal import Decimal, localcontext

from formal.python.evm_builtins import WORD_MOD, eval_pure_builtin, u256

WAD = 10**18
RAY = 10**27
SIGN_BIT = 1 << 255

# x = WAD + 1 is the witness input for the floor specification: the exact result lies
# strictly inside (10**9 - 1, 10**9), so any rounding mode other than floor (or floor - 1)
# is detectable here.
WITNESS_X = WAD + 1
EXPECTED_FLOOR_RESULT = 10**9 - 1

# Constants mirrored from src/vendor/Ln.sol (see the comments there for derivations).
_S = 0xB504F333F9DE6484597D89B3
_P4 = 0xF642B0ED5372FF45E0
_P3 = 0xEDE142E73A9ACBB00E9C42
_P2 = 0xF2A56533E74A454C9D585F70
_P1 = 0xB44D9253CD61FB87DC7EFCFC
_C0 = 0xB05A8B41CF51C04D1B8A08D473
_Q4 = 0x364589193443B48661938F59DC
_Q3 = 0xE904C4E76307954DF78FEF
_Q2 = 0xAD960AB2F600BD9765C15FFD
_Q1 = 0xD1B1FEDEC544F0EA0BC812BBCA
_K = 0x6765C793FA10079D
_LN2 = 0x23D5B9FF36551802AA5D6F9754B0F3FAD83B19450
_BIAS = 0x4FF7E9B32826A6AEC97EA1E696BD71EB764C77277C


def _op(name: str, *args: int) -> int:
    return eval_pure_builtin(name, tuple(args))


def _i256(word: int) -> int:
    word = u256(word)
    return word - WORD_MOD if word >= SIGN_BIT else word


def ln_wad_evm(x: int) -> int:
    """Step-for-step mirror of `Ln.lnWadToRay` from src/vendor/Ln.sol (wad in, ray out)."""
    x_word = u256(x)
    if _op("iszero", _op("sgt", x_word, 0)) != 0:
        raise ValueError("LnWadUndefined")

    c = _op("clz", x_word)
    k = _op("sub", 0xA0, c)
    x_word = _op("shr", 0xA0, _op("shl", c, x_word))

    z = _op("sdiv", _op("shl", 0x64, _op("sub", _S, x_word)), _op("add", x_word, _S))
    u = _op("shr", 0x68, _op("mul", z, z))

    p = _op("sub", _op("shr", 0x54, _op("mul", _P4, u)), _P3)
    p = _op("add", _op("sar", 0x5A, _op("mul", p, u)), _P2)
    p = _op("sub", _op("sar", 0x61, _op("mul", p, u)), _P1)
    p = _op("add", _op("sar", 0x57, _op("mul", p, u)), _C0)

    q = _op("sub", u, _Q4)
    q = _op("add", _op("sar", 0x71, _op("mul", q, u)), _Q3)
    q = _op("sub", _op("sar", 0x5A, _op("mul", q, u)), _Q2)
    q = _op("add", _op("sar", 0x58, _op("mul", q, u)), _Q1)
    q = _op("sub", _op("sar", 0x5F, _op("mul", q, u)), _C0)

    r = _op("sdiv", _op("mul", p, z), q)
    r = _op("mul", r, _K)
    r = _op("add", r, _op("mul", _LN2, k))
    r = _op("add", r, _BIAS)
    r = _op("sar", 0x48, r)
    # lnWadToRay(10**18) = 0 is the only integer-valued result; the floored
    # accumulator lands on -1 there. `iszero(not(r))` adds 1 back exactly when
    # r == -1 (and never otherwise), giving the exact 0.
    return _i256(_op("add", _op("iszero", _op("not", r)), r))


def ln_wad_to_wad_evm(x: int) -> int:
    """Step-for-step mirror of `Ln.lnWad` from src/vendor/Ln.sol (wad in, wad out)."""
    r = u256(ln_wad_evm(x))
    return _i256(
        _op("sdiv", _op("sub", r, _op("mul", _op("slt", r, 0), 0x3B9AC9FF)), 0x3B9ACA00)
    )


def floor_spec_for_witness(x: int) -> int:
    if x != WAD + 1:
        raise ValueError("exact floor proof is specialized to WAD + 1")

    # For t > 0, t - t**2/2 < ln(1 + t) < t. With t = 1 / WAD, the exact value
    # RAY * ln(1 + t) lies in (10**9 - 5e-10, 10**9), so its floor is 10**9 - 1.
    return 10**9 - 1


def decimal_ln_ray(x: int) -> Decimal:
    with localcontext() as ctx:
        ctx.prec = 120
        return (Decimal(x) / Decimal(WAD)).ln() * Decimal(RAY)


def main() -> int:
    actual = ln_wad_evm(WITNESS_X)
    expected = floor_spec_for_witness(WITNESS_X)
    value = decimal_ln_ray(WITNESS_X)

    assert expected == EXPECTED_FLOOR_RESULT, expected
    # lnWadToRay must return floor(L) or floor(L) - 1.
    assert actual in (expected, expected - 1), actual
    # ln(10**18 / 10**18) = 0 exactly, and the implementation pins it.
    assert ln_wad_evm(WAD) == 0
    assert ln_wad_to_wad_evm(WAD) == 0
    # The wad-basis helper floors the ray result by 10**9 in both sign regimes.
    assert ln_wad_to_wad_evm(WITNESS_X) in (0, -1)
    assert ln_wad_to_wad_evm(WAD - 1) == -2  # ray result -1000000001 floors to -2

    print(f"x = {WITNESS_X}")
    print(f"lnWadToRay EVM result = {actual}")
    print(f"floor mathematical result = {expected}")
    print(f"1e27 * ln(x / 1e18) = {value}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
