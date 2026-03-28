"""Shared lnQ256 utilities for the relaxed stage-1 bounds tooling."""

from __future__ import annotations

from dataclasses import dataclass
from typing import List

import mpmath as mp

N0 = [31, 29, 28, 26, 25, 24, 23, 22, 21, 20, 19, 19, 18, 17, 17, 16]
SCALE = 1 << 256


def _round_div(num: int, den: int) -> int:
    if den <= 0:
        raise ValueError("den must be positive")
    if num >= 0:
        return (num + den // 2) // den
    return -(((-num) + den // 2) // den)


def _floor_div_pow2_signed(x: int, shift: int) -> int:
    if x >= 0:
        return x >> shift
    return -(((-x) + (1 << shift) - 1) >> shift)


def _mulshr_round(a: int, b: int, shift: int) -> int:
    prod = a * b
    if prod >= 0:
        return (prod + (1 << (shift - 1))) >> shift
    return -(((-prod) + (1 << (shift - 1))) >> shift)


def _mulshr_floor(a: int, b: int, shift: int) -> int:
    prod = a * b
    if prod >= 0:
        return prod >> shift
    return -(((-prod) + (1 << shift) - 1) >> shift)


def _qmul_coeff(a_qc: int, b_q256: int) -> int:
    return _mulshr_round(a_qc, b_q256, 256)


@dataclass(frozen=True)
class CoarseState:
    exponent: int
    bucket: int
    coarse_num: int
    u_num: int
    z_den: int


def extract_state(x: int) -> CoarseState:
    if x <= 0:
        raise ValueError("x must be positive")
    e = x.bit_length() - 1
    j = ((x << (4 - e)) & 0xF) if e < 4 else ((x >> (e - 4)) & 0xF)
    n = N0[j]
    u_num = n * x - (1 << (e + 5))
    z_den = (1 << (e + 6)) + u_num
    return CoarseState(e, j, n, u_num, z_den)


def hard_boundary_family() -> List[int]:
    """Inputs engineered to sit near Q256 integer boundaries."""
    saved = mp.mp.dps
    mp.mp.dps = max(saved, 420)
    out: List[int] = []
    seen = set()
    for b in range(279, 512):
        n = int(mp.nint(mp.mpf(b) * mp.log(2) * (mp.mpf(2) ** 256)))
        x = int(mp.nint(mp.e ** (mp.mpf(n) / (mp.mpf(2) ** 256))))
        if x not in seen:
            out.append(x)
            seen.add(x)
    mp.mp.dps = saved
    return out
