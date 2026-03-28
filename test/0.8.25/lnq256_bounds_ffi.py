#!/usr/bin/env python3
"""FFI oracle for relaxed lnQ256 lower/upper bound differential testing.

Usage:
    python3 test/0.8.25/lnq256_bounds_ffi.py <x_hi_hex> <x_lo_hex>

Outputs 0x-prefixed ABI-encoded:
    (floor_hi, floor_lo, ceil_hi, ceil_lo)
where floor = floor(ln(x) * 2^256) and ceil = ceil(ln(x) * 2^256).
"""

import sys
import mpmath as mp


def true_floor_ceil_ln_q256(x: int) -> tuple[int, int]:
    if x <= 0:
        raise ValueError("x must be positive")
    if x == 1:
        return 0, 0

    last_floor = None
    last_ceil = None
    for dps in (220, 320, 420):
        mp.mp.dps = dps
        y = mp.log(mp.mpf(x)) * (mp.mpf(2) ** 256)
        cur_floor = int(mp.floor(y))
        cur_ceil = int(mp.ceil(y))
        if cur_floor == last_floor and cur_ceil == last_ceil:
            return cur_floor, cur_ceil
        last_floor = cur_floor
        last_ceil = cur_ceil
    return last_floor, last_ceil


def main() -> None:
    x_hi = int(sys.argv[1], 16)
    x_lo = int(sys.argv[2], 16)
    x = (x_hi << 256) | x_lo
    if x == 0:
        raise ValueError("x must be positive")

    floor_q256, ceil_q256 = true_floor_ceil_ln_q256(x)
    floor_hi = floor_q256 >> 256
    floor_lo = floor_q256 & ((1 << 256) - 1)
    ceil_hi = ceil_q256 >> 256
    ceil_lo = ceil_q256 & ((1 << 256) - 1)

    out = (
        floor_hi.to_bytes(32, "big")
        + floor_lo.to_bytes(32, "big")
        + ceil_hi.to_bytes(32, "big")
        + ceil_lo.to_bytes(32, "big")
    )
    sys.stdout.write("0x" + out.hex())


if __name__ == "__main__":
    main()
