#!/usr/bin/env python3
"""
Rigorous verification of _sqrt convergence in Sqrt.sol.

Proves: for all x in [1, 2^256 - 1], after 6 truncated Babylonian steps
starting from seed z_0 = 2^floor((n+1)/2), the result z_6 satisfies

    isqrt(x) <= z_6 <= isqrt(x) + 1

i.e., z_6 in {floor(sqrt(x)), ceil(sqrt(x))}.

Proof structure:

  Lemma 1 (Floor Bound): Each truncated Babylonian step satisfies z' >= isqrt(x).
    Proved algebraically (AM-GM + integrality). Spot-checked here.

  Lemma 2 (Absorbing Set): If z in {isqrt(x), isqrt(x)+1}, then z' in {isqrt(x), isqrt(x)+1}.
    Proved algebraically. Spot-checked here.

  Lemma 3 (Convergence): After 6 steps from the seed, z_6 <= isqrt(x) + 1.
    Proved by upper-bound recurrence on absolute error e_i = z_i - sqrt(x):
      Step 0->1: U_1 = max|e_0|^2 / (2*z_0)   [exact, since sqrt(x) + e_0 = z_0]
      Step i->i+1: U_{i+1} = max(U_i^2 / (2*(r_lo + U_i)), 1 / (2*(r_lo - 1)))
    Verified U_6 < 1 for all octaves n in [2, 255].
    Octaves n in [0, 1] covered by exhaustive check.

  Theorem: _sqrt(x) in {isqrt(x), isqrt(x) + 1} for all x in [0, 2^256 - 1].

Usage:
    python3 verify_sqrt.py
"""

import math
import sys
from mpmath import mp, mpf, sqrt as mp_sqrt

# High precision for rigorous sqrt computation
mp.prec = 1000  # ~300 decimal digits


# =========================================================================
# EVM semantics
# =========================================================================

def isqrt(x):
    """Exact integer square root (Python 3.8+)."""
    return math.isqrt(x)


def evm_seed(n):
    """
    Seed for octave n (MSB position of x).
    z_0 = 2^floor((n+1)/2).
    Corresponds to: shl(shr(1, sub(256, clz(x))), 1)
    """
    return 1 << ((n + 1) >> 1)


def babylon_step(x, z):
    """One truncated Babylonian step: floor((z + floor(x/z)) / 2)."""
    if z == 0:
        return 0
    return (z + x // z) // 2


def full_sqrt(x):
    """
    Run the full _sqrt algorithm: seed + 6 Babylonian steps.
    Returns z_6.

    Note: for x=0 the EVM code returns 0 because div(0,0)=0 in EVM.
    Python would throw, so we handle x=0 specially.
    """
    if x == 0:
        return 0
    n = x.bit_length() - 1  # MSB position
    z = evm_seed(n)
    for _ in range(6):
        z = babylon_step(x, z)
    return z


# =========================================================================
# Part 1: Exhaustive verification for small octaves
# =========================================================================

def verify_exhaustive(max_n=20):
    """Exhaustively verify _sqrt for all x in octaves n = 0..max_n."""
    print(f"Part 1: Exhaustive verification for n <= {max_n}")
    print("-" * 60)

    # x = 0: EVM div(0,0)=0, so z -> 0. isqrt(0) = 0. Correct.
    print("  x=0: z=0, isqrt(0)=0. OK")

    all_ok = True
    for n in range(max_n + 1):
        x_lo = 1 << n
        x_hi = (1 << (n + 1)) - 1

        failures = 0
        for x in range(x_lo, x_hi + 1):
            z = full_sqrt(x)
            s = isqrt(x)
            if z != s and z != s + 1:
                print(f"  FAIL: n={n}, x={x}, z6={z}, isqrt={s}")
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
    """
    For each octave n >= min_n, compute U_6 and verify U_6 < 1.

    Upper bound recurrence on e = z - sqrt(x):

      U_1 = max|e_0|^2 / (2 * z_0)
        Tight because sqrt(x) + e_0 = z_0 is constant.

      U_{i+1} = max( U_i^2 / (2*(r_lo + U_i)),  1 / (2*(r_lo - 1)) )
        Decorrelated: allows e_i in [-1, U_i] independently of sqrt(x).
        Sound because:
          - e_{i+1} <= e_i^2 / (2*(sqrt(x) + e_i))  [exact step is upper bound]
          - e_i >= -1 for i >= 1                      [Lemma 1]
          - maximizing over (e, r) decoupled gives the formula above

    For n >= 2: r_lo = sqrt(2^n) = 2^(n/2) >= 2, so 1/(2*(r_lo-1)) <= 1/2 < 1.
    """
    print(f"Part 2: Upper bound propagation for n >= {min_n}")
    print("-" * 60)

    all_ok = True
    worst_n = -1
    worst_ratio = mpf(0)

    for n in range(min_n, 256):
        x_lo = 1 << n
        z0 = evm_seed(n)

        # Real-valued sqrt bounds
        r_lo = mp_sqrt(mpf(x_lo))
        r_hi = mp_sqrt(mpf((1 << (n + 1)) - 1))

        # Step 0: e_0 = z_0 - sqrt(x), ranges over the octave
        e0_at_lo = mpf(z0) - r_lo   # error at x = x_lo
        e0_at_hi = mpf(z0) - r_hi   # error at x = x_hi
        max_abs_e0 = max(abs(e0_at_lo), abs(e0_at_hi))

        # Step 0 -> 1: tight bound (denominator is constant z_0)
        U = max_abs_e0 ** 2 / (2 * mpf(z0))

        # Steps 1->2 through 5->6: decorrelated bound
        floor_bounce = mpf(1) / (2 * (r_lo - 1))

        for _step in range(5):  # 5 more steps (1->2, ..., 5->6)
            quadratic_term = U ** 2 / (2 * (r_lo + U))
            U = max(quadratic_term, floor_bounce)

        ok = U < 1
        if not ok:
            all_ok = False

        ratio = U  # U_6: absolute error bound
        if ratio > worst_ratio:
            worst_ratio = ratio
            worst_n = n

        # Print selected octaves
        if not ok or n <= 5 or n >= 250 or n % 50 == 0:
            tag = "OK" if ok else "FAIL"
            print(f"  n={n:>3}: z0=2^{(n+1)>>1}, |e0|_max={float(max_abs_e0):.4e}, "
                  f"U6={float(U):.4e}  [{tag}]")

    print(f"\n  Worst: n={worst_n}, U6={float(worst_ratio):.6e}")
    print()
    return all_ok


# =========================================================================
# Part 3: Spot-check Lemma 1 (floor bound)
# =========================================================================

def verify_floor_bound():
    """
    Spot-check: z' = floor((z + floor(x/z)) / 2) >= isqrt(x) for z >= 1, x >= 1.

    Algebraic proof (Lean-portable):
      1. s = z + floor(x/z) is a positive integer
      2. floor(x/z) >= (x - z + 1)/z = x/z - 1 + 1/z
         so s >= z + x/z - 1 + 1/z > 2*sqrt(x) - 1  (AM-GM + 1/z > 0)
      3. s is integer and s > 2*isqrt(x) - 1  (since sqrt(x) >= isqrt(x))
         therefore s >= 2*isqrt(x)
      4. floor(s/2) >= isqrt(x)
    """
    print("Part 3: Spot-check floor bound (z' >= isqrt(x))")
    print("-" * 60)

    import random
    random.seed(42)

    test_cases = []

    # Edge cases
    for x in [1, 2, 3, 4, 100]:
        for z in [1, 2, 3, max(1, isqrt(x) - 1), isqrt(x), isqrt(x) + 1, isqrt(x) + 2, x]:
            if z >= 1:
                test_cases.append((x, z))

    # Large values
    test_cases.append(((1 << 256) - 1, 1 << 128))
    test_cases.append(((1 << 256) - 1, (1 << 128) - 1))
    test_cases.append(((1 << 254), 1 << 127))

    # Random large
    for _ in range(500):
        x = random.randint(1, (1 << 256) - 1)
        z = random.randint(1, min(x, (1 << 200)))
        test_cases.append((x, z))

    # Near-isqrt (most interesting)
    for _ in range(500):
        x = random.randint(1, (1 << 256) - 1)
        s = isqrt(x)
        for z in [max(1, s - 1), s, s + 1, s + 2]:
            test_cases.append((x, z))

    failures = 0
    for x, z in test_cases:
        z_next = babylon_step(x, z)
        s = isqrt(x)
        if z_next < s:
            print(f"  FAIL: x={x}, z={z}, z'={z_next}, isqrt={s}")
            failures += 1

    if failures == 0:
        print(f"  {len(test_cases)} test cases, all satisfy z' >= isqrt(x). OK")
    else:
        print(f"  {failures} FAILURES")
    print()
    return failures == 0


# =========================================================================
# Part 4: Spot-check Lemma 2 (absorbing set)
# =========================================================================

def verify_absorbing_set():
    """
    Spot-check: if z in {m, m+1} where m = isqrt(x), then z' in {m, m+1}.

    Algebraic proof (Lean-portable):
      Let m = isqrt(x), so m^2 <= x < (m+1)^2.

      Case z = m+1:
        floor(x/(m+1)) <= m  (since x < (m+1)^2)
        s = (m+1) + floor(x/(m+1)) <= 2m+1
        floor(s/2) <= m
        Combined with Lemma 1 (z' >= m): z' = m.

      Case z = m:
        floor(x/m) in {m, m+1, m+2}  (since m^2 <= x < m^2 + 2m + 1)
        s = m + floor(x/m) in {2m, 2m+1, 2m+2}
        floor(s/2) in {m, m, m+1}
        So z' in {m, m+1}.
    """
    print("Part 4: Spot-check absorbing set {isqrt(x), isqrt(x)+1}")
    print("-" * 60)

    import random
    random.seed(123)

    failures = 0
    count = 0

    # Random large cases
    for _ in range(5000):
        x = random.randint(1, (1 << 256) - 1)
        m = isqrt(x)
        for z in [m, m + 1]:
            z_next = babylon_step(x, z)
            if z_next != m and z_next != m + 1:
                print(f"  FAIL: x={x}, z={z}, z'={z_next}, isqrt={m}")
                failures += 1
            count += 1

    # Small cases exhaustively
    for x in range(1, 10001):
        m = isqrt(x)
        for z in [m, m + 1]:
            z_next = babylon_step(x, z)
            if z_next != m and z_next != m + 1:
                print(f"  FAIL: x={x}, z={z}, z'={z_next}, isqrt={m}")
                failures += 1
            count += 1

    if failures == 0:
        print(f"  {count} test cases, absorbing set holds. OK")
    else:
        print(f"  {failures} FAILURES")
    print()
    return failures == 0


# =========================================================================
# Part 5: Print proof summary
# =========================================================================

def print_proof_summary():
    print("=" * 60)
    print("PROOF SUMMARY")
    print("=" * 60)
    print("""
Theorem: For all x in [0, 2^256 - 1],
  _sqrt(x) in {isqrt(x), isqrt(x) + 1}.

Proof:

  Case x = 0: seed=1, div(0,1)=0, then div(0,0)=0 (EVM).
  Result z=0 = isqrt(0). Done.

  Case x >= 1: Let n = floor(log2(x)), z_0 = 2^floor((n+1)/2).

  Lemma 1 (Floor Bound):
    For any x >= 1, z >= 1:
      z' = floor((z + floor(x/z)) / 2) >= isqrt(x).
    Proof:
      s = z + floor(x/z) is a positive integer.
      floor(x/z) >= x/z - 1 + 1/z (remainder bound).
      s > z + x/z - 1 >= 2*sqrt(x) - 1 (AM-GM).
      Since sqrt(x) >= isqrt(x), s > 2*isqrt(x) - 1.
      s integer => s >= 2*isqrt(x).
      floor(s/2) >= isqrt(x).  QED.

    Corollary: z_i >= isqrt(x) for all i >= 1.

  Lemma 2 (Absorbing Set):
    If z in {m, m+1} where m = isqrt(x), then z' in {m, m+1}.
    (Proved by case analysis on z = m and z = m+1.)

  Lemma 3 (Convergence):
    After 6 steps, z_6 <= isqrt(x) + 1.
    Proof: Track upper bound U on e = z - sqrt(x).
      U_1 = max|e_0|^2 / (2*z_0).
      U_{i+1} = max(U_i^2/(2*(r_lo+U_i)), 1/(2*(r_lo-1))).
      Computed: U_6 < 1 for all n in [2, 255].
      n in {0, 1}: verified exhaustively.
    Since z_6 < sqrt(x) + 1 and z_6 is integer:
      z_6 <= ceil(sqrt(x)) = isqrt(x) + 1  (non-perfect-square)
      z_6 <= sqrt(x) + 1 => z_6 <= isqrt(x) + 1  (perfect square)

  Combining Lemmas 1 + 3:
    isqrt(x) <= z_6 <= isqrt(x) + 1.  QED.
""")


# =========================================================================
# Main
# =========================================================================

def main():
    print("=" * 60)
    print("Rigorous Verification: _sqrt (Sqrt.sol)")
    print("=" * 60)
    print()

    ok1 = verify_exhaustive(max_n=20)
    ok2 = verify_upper_bound(min_n=2)
    ok3 = verify_floor_bound()
    ok4 = verify_absorbing_set()

    all_ok = ok1 and ok2 and ok3 and ok4

    if all_ok:
        print_proof_summary()
        print("ALL CHECKS PASSED.")
    else:
        print("SOME CHECKS FAILED.")

    print("=" * 60)
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
