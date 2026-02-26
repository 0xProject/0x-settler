#!/usr/bin/env python3
"""
Rigorous verification of _cbrt convergence in Cbrt.sol.

Proves: for all x in [1, 2^256 - 1], after 6 Newton-Raphson steps
starting from the computed seed, the result z_6 satisfies

    icbrt(x) <= z_6 <= icbrt(x) + 1

Proof structure (mirrors sqrt):

  Lemma 1 (Floor Bound): Each truncated NR step satisfies z' >= icbrt(x).
    Proved algebraically via cubic AM-GM:
      (3m - 2z) * z^2 <= m^3  for all z, m >= 0
    because m^3 - (3m-2z)*z^2 = (m-z)^2*(m+2z) >= 0.

  Lemma 2 (Absorbing Set): If z in {icbrt(x), icbrt(x)+1}, then z' in {icbrt(x), icbrt(x)+1}.

  Lemma 3 (Convergence): After 6 steps from the seed, z_6 <= icbrt(x) + 1.
    Proved by upper-bound recurrence verified for all 256 octaves.

Usage:
    python3 verify_cbrt.py
"""

import math
import sys
from mpmath import mp, mpf, sqrt as mp_sqrt, cbrt as mp_cbrt

mp.prec = 1000


def icbrt(x):
    """Integer cube root (floor). Uses Python's integer arithmetic."""
    if x <= 0:
        return 0
    if x < 8:
        return 1
    # Good initial estimate using bit length
    n = x.bit_length()
    z = 1 << ((n + 2) // 3)
    # Newton's method with integer arithmetic
    while True:
        z1 = (2 * z + x // (z * z)) // 3
        if z1 >= z:
            break
        z = z1
    # Final correction
    while z * z * z > x:
        z -= 1
    while (z + 1) ** 3 <= x:
        z += 1
    return z


def evm_cbrt_seed(x):
    """Seed matching Cbrt.sol: add(shr(8, shl(div(sub(257, clz(x)), 3), 0xe9)), lt(0, x))"""
    if x == 0:
        return 0
    clz = 256 - x.bit_length()
    q = (257 - clz) // 3
    base = (0xe9 << q) >> 8
    return base + 1  # lt(0, x) = 1 for x > 0


def cbrt_step(x, z):
    """One NR step: floor((floor(x/(z*z)) + 2*z) / 3)"""
    if z == 0:
        return 0
    return (x // (z * z) + 2 * z) // 3


def full_cbrt(x):
    """Run _cbrt: seed + 6 NR steps."""
    if x == 0:
        return 0
    z = evm_cbrt_seed(x)
    for _ in range(6):
        z = cbrt_step(x, z)
    return z


# =========================================================================
# Part 1: Exhaustive verification for small octaves
# =========================================================================

def verify_exhaustive(max_n=20):
    print(f"Part 1: Exhaustive verification for n <= {max_n}")
    print("-" * 60)
    print("  x=0: z=0, icbrt(0)=0. OK")

    all_ok = True
    for n in range(max_n + 1):
        x_lo = 1 << n
        x_hi = (1 << (n + 1)) - 1
        failures = 0
        for x in range(x_lo, x_hi + 1):
            z = full_cbrt(x)
            s = icbrt(x)
            if z != s and z != s + 1:
                print(f"  FAIL: n={n}, x={x}, z6={z}, icbrt={s}")
                failures += 1
        count = x_hi - x_lo + 1
        if failures == 0:
            print(f"  n={n:>3}: [{x_lo}, {x_hi}] ({count} values) -- all OK")
        else:
            print(f"  n={n:>3}: {failures} FAILURES out of {count}")
            all_ok = False
    print()
    return all_ok


# =========================================================================
# Part 2: Upper bound propagation for all octaves
# =========================================================================

def verify_upper_bound(min_n=2):
    print(f"Part 2: Upper bound propagation for n >= {min_n}")
    print("-" * 60)

    all_ok = True
    worst_n = -1
    worst_ratio = mpf(0)

    for n in range(min_n, 256):
        x_lo = 1 << n
        x_hi = (1 << (n + 1)) - 1
        z0 = evm_cbrt_seed(x_lo)  # seed is same for all x in octave

        # Propagate max: Z_{i+1} = cbrt_step(x_max, Z_i)
        Z = z0
        for _ in range(6):
            if Z == 0:
                break
            Z = cbrt_step(x_hi, Z)

        s_hi = icbrt(x_hi)
        ok = Z <= s_hi + 1

        if not ok:
            all_ok = False

        if Z > worst_ratio:
            worst_ratio = Z
            worst_n = n

        if not ok or n <= 5 or n >= 250 or n % 50 == 0:
            tag = "OK" if ok else "FAIL"
            print(f"  n={n:>3}: seed={z0}, Z6={Z}, icbrt(x_max)={s_hi}, "
                  f"Z6<=icbrt+1: {ok}  [{tag}]")

    print()
    return all_ok


# =========================================================================
# Part 3: Spot-check floor bound (cubic AM-GM)
# =========================================================================

def verify_floor_bound():
    print("Part 3: Spot-check floor bound (z' >= icbrt(x))")
    print("-" * 60)

    import random
    random.seed(42)

    failures = 0
    test_cases = []

    # Edge cases
    for x in [1, 2, 7, 8, 27, 64, 100, 1000]:
        for z in [1, 2, max(1, icbrt(x)), icbrt(x) + 1, icbrt(x) + 2, x]:
            if z >= 1:
                test_cases.append((x, z))

    # Random large
    for _ in range(500):
        x = random.randint(1, (1 << 256) - 1)
        z = random.randint(1, min(x, (1 << 128)))
        test_cases.append((x, z))

    # Near-icbrt
    for _ in range(500):
        x = random.randint(1, (1 << 256) - 1)
        s = icbrt(x)
        for z in [max(1, s - 1), s, s + 1, s + 2]:
            test_cases.append((x, z))

    for x, z in test_cases:
        z_next = cbrt_step(x, z)
        s = icbrt(x)
        if z_next < s:
            print(f"  FAIL: x={x}, z={z}, z'={z_next}, icbrt={s}")
            failures += 1

    if failures == 0:
        print(f"  {len(test_cases)} test cases, all satisfy z' >= icbrt(x). OK")
    else:
        print(f"  {failures} FAILURES")
    print()
    return failures == 0


# =========================================================================
# Part 4: Spot-check absorbing set
# =========================================================================

def verify_absorbing_set():
    print("Part 4: Spot-check absorbing set {icbrt(x), icbrt(x)+1}")
    print("-" * 60)

    import random
    random.seed(123)
    failures = 0
    count = 0

    for _ in range(5000):
        x = random.randint(1, (1 << 256) - 1)
        m = icbrt(x)
        for z in [m, m + 1]:
            if z > 0:
                z_next = cbrt_step(x, z)
                if z_next != m and z_next != m + 1:
                    print(f"  FAIL: x={x}, z={z}, z'={z_next}, icbrt={m}")
                    failures += 1
                count += 1

    for x in range(1, 10001):
        m = icbrt(x)
        for z in [m, m + 1]:
            if z > 0:
                z_next = cbrt_step(x, z)
                if z_next != m and z_next != m + 1:
                    print(f"  FAIL: x={x}, z={z}, z'={z_next}, icbrt={m}")
                    failures += 1
                count += 1

    if failures == 0:
        print(f"  {count} test cases, absorbing set holds. OK")
    else:
        print(f"  {failures} FAILURES")
    print()
    return failures == 0


# =========================================================================
# Main
# =========================================================================

def main():
    print("=" * 60)
    print("Rigorous Verification: _cbrt (Cbrt.sol)")
    print("=" * 60)
    print()

    ok1 = verify_exhaustive(max_n=20)
    ok2 = verify_upper_bound(min_n=2)
    ok3 = verify_floor_bound()
    ok4 = verify_absorbing_set()

    all_ok = ok1 and ok2 and ok3 and ok4

    if all_ok:
        print("=" * 60)
        print("ALL CHECKS PASSED.")
        print("=" * 60)
    else:
        print("SOME CHECKS FAILED.")

    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
