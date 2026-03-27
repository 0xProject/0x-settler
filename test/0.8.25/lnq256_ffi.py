#!/usr/bin/env python3
"""FFI oracle for LnQ256 differential fuzz testing.

Usage:
    python3 test/0.8.25/lnq256_ffi.py <x_hi_hex> <x_lo_hex>

Outputs 0x-prefixed ABI-encoded (uint256, uint256) = (result_hi, result_lo)
where result = floor(ln(x) * 2^256) and x = x_hi * 2^256 + x_lo.
"""

import sys
import mpmath as mp


def true_floor_ln_q256(x: int) -> int:
    """Compute floor(ln(x) * 2^256) using mpmath at sufficient precision."""
    if x <= 0:
        raise ValueError("x must be positive")
    if x == 1:
        return 0
    last = None
    for dps in (220, 320, 420):
        mp.mp.dps = dps
        cur = int(mp.floor(mp.log(mp.mpf(x)) * (mp.mpf(2) ** 256)))
        if cur == last:
            return cur
        last = cur
    return last


def main() -> None:
    x_hi = int(sys.argv[1], 16)
    x_lo = int(sys.argv[2], 16)
    x = (x_hi << 256) | x_lo

    if x == 0:
        raise ValueError("x must be positive")

    result = true_floor_ln_q256(x)
    hi = result >> 256
    lo = result & ((1 << 256) - 1)

    out = hi.to_bytes(32, "big") + lo.to_bytes(32, "big")
    sys.stdout.write("0x" + out.hex())


if __name__ == "__main__":
    main()
