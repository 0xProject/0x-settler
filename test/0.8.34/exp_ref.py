#!/usr/bin/env python3
"""High-precision reference for Exp.expRayToWad, used as the differential oracle over FFI.

Prints floor(10**18 * exp(x / 10**27)) for the int256 argument `x`, ABI-encoded as a single
32-byte word (hex). The result is always non-negative over the tested range.
"""
import sys
import mpmath as mp

mp.mp.dps = 120


def main() -> None:
    x = int(sys.argv[1])
    value = int(mp.floor(mp.mpf(10) ** 18 * mp.e ** (mp.mpf(x) / mp.mpf(10) ** 27)))
    print("0x" + format(value & ((1 << 256) - 1), "064x"))


if __name__ == "__main__":
    main()
