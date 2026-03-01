#!/usr/bin/env python3
"""
Generate finite-certificate tables for the sqrt formal proof.

For each of 256 octaves (n = 0..255), where octave n contains x in [2^n, 2^(n+1) - 1]:
  - loOf(n) = isqrt(2^n)           -- lower bound on isqrt(x)
  - hiOf(n) = isqrt(2^(n+1) - 1)  -- upper bound on isqrt(x)
  - seedOf(n) = 1 << ((n+1)/2)    -- sqrt seed for octave n
  - d1(n): first-step error bound from algebraic formula
  - d2..d6(n): chained via nextD(lo, d) = d^2/(2*lo) + 1

The d1 bound uses the quadratic identity:
    (z1 - m)^2 ≤ (s - m)^2 + 2*m*(m+1)/s * ((s-m)^2 / (2*m))
    ≤ maxAbs^2 + 2*hi
where maxAbs = max(|s-lo|, |hi-s|).
So d1 = (maxAbs^2 + 2*hi) / (2*seed).

Also generates a Sqrt512Cert namespace with fixed-seed certificates for
octaves 254/255, used by the 512-bit sqrt proof.
"""

import argparse
import sys


def isqrt(x):
    """Integer square root (floor)."""
    if x <= 0:
        return 0
    if x < 4:
        return 1
    n = x.bit_length()
    z = 1 << ((n + 1) // 2)
    while True:
        z1 = (z + x // z) // 2
        if z1 >= z:
            break
        z = z1
    while z * z > x:
        z -= 1
    while (z + 1) ** 2 <= x:
        z += 1
    return z


def sqrt_step(x, z):
    """One Babylonian step: floor((z + floor(x/z)) / 2)"""
    if z == 0:
        return 0
    return (z + x // z) // 2


def sqrt_seed(n):
    """Seed for octave n: 1 << ((n+1)/2)."""
    return 1 << ((n + 1) // 2)


def next_d(lo, d):
    """Error recurrence: d^2/(2*lo) + 1."""
    if lo == 0:
        return d * d + 1
    return d * d // (2 * lo) + 1


def compute_maxabs(lo, hi, s):
    """max(|s - lo|, |hi - s|)"""
    return max(abs(s - lo), abs(hi - s))


def compute_d1(lo, hi, s):
    """Analytic d1 bound:
    d1 = floor((maxAbs^2 + 2*hi) / (2*s))
    """
    maxAbs = compute_maxabs(lo, hi, s)
    numerator = maxAbs * maxAbs + 2 * hi
    denominator = 2 * s
    if denominator == 0:
        return 0
    return numerator // denominator


def main():
    parser = argparse.ArgumentParser(
        description="Generate finite-certificate tables for sqrt formal proof"
    )
    parser.add_argument(
        "--output",
        default="SqrtProof/SqrtProof/FiniteCert.lean",
        help="Output Lean file path (default: SqrtProof/SqrtProof/FiniteCert.lean)",
    )
    args = parser.parse_args()

    lo_table = []
    hi_table = []

    for n in range(256):
        lo = isqrt(1 << n)
        hi = isqrt((1 << (n + 1)) - 1)
        lo_table.append(lo)
        hi_table.append(hi)

    # Verify basic properties
    for n in range(256):
        lo = lo_table[n]
        hi = hi_table[n]
        assert lo * lo <= (1 << n), f"lo^2 > 2^n at n={n}"
        assert (1 << (n + 1)) <= (hi + 1) ** 2, f"2^(n+1) > (hi+1)^2 at n={n}"
        assert lo <= hi, f"lo > hi at n={n}"

    # Compute certificate for all 256 octaves
    all_ok = True
    d_data = {}  # n -> (d1, ..., d6)

    for n in range(256):
        lo = lo_table[n]
        hi = hi_table[n]
        seed = sqrt_seed(n)

        d1 = compute_d1(lo, hi, seed)
        d2 = next_d(lo, d1)
        d3 = next_d(lo, d2)
        d4 = next_d(lo, d3)
        d5 = next_d(lo, d4)
        d6 = next_d(lo, d5)
        d_data[n] = (d1, d2, d3, d4, d5, d6)

        if d6 > 1:
            print(f"FAIL d6: n={n}, d1={d1}, d2={d2}, d3={d3}, "
                  f"d4={d4}, d5={d5}, d6={d6}, lo={lo}")
            all_ok = False

        # Check side conditions: dk <= lo for k=1..5
        for k, dk in enumerate([d1, d2, d3, d4, d5], 1):
            if dk > lo:
                print(f"SIDE FAIL: n={n}, d{k}={dk} > lo={lo}")
                all_ok = False

    if all_ok:
        print(f"All octaves 0-255 pass: d6 <= 1, all side conditions OK.")
    else:
        print("SOME OCTAVES FAIL.")

    # Exhaustive verification for small octaves to confirm d1 bound
    print(f"\nExhaustive verification of d1 for octaves 0-30...")
    for n in range(min(31, 256)):
        lo = lo_table[n]
        hi = hi_table[n]
        seed = sqrt_seed(n)
        d1_cert = d_data[n][0]

        for m in range(lo, hi + 1):
            x_lo_m = max(m * m, 1 << n)
            x_hi_m = min((m + 1) ** 2 - 1, (1 << (n + 1)) - 1)
            if x_lo_m > x_hi_m:
                continue
            z1 = sqrt_step(x_hi_m, seed)  # max z1 by mono in x
            actual_d1 = max(0, z1 - m)
            if actual_d1 > d1_cert:
                print(f"  D1 FAIL: n={n}, m={m}, z1={z1}, actual_d1={actual_d1}, cert={d1_cert}")
                all_ok = False
    print("  d1 exhaustive check done.")

    # Spot-check d1 for large octaves
    import random
    random.seed(42)
    print("\nSpot-checking d1 for large octaves...")
    for n in range(100, 256, 10):
        lo = lo_table[n]
        hi = hi_table[n]
        seed = sqrt_seed(n)
        d1_cert = d_data[n][0]

        for m in [lo, hi, lo + (hi - lo) // 3, lo + 2 * (hi - lo) // 3]:
            x_max = min((m + 1) ** 2 - 1, (1 << (n + 1)) - 1)
            x_min = max(m ** 2, 1 << n)
            if x_min > x_max:
                continue
            z1 = sqrt_step(x_max, seed)
            actual_d1 = max(0, z1 - m)
            if actual_d1 > d1_cert:
                print(f"  SPOT FAIL: n={n}, m={m}, z1={z1}, actual_d1={actual_d1}, cert={d1_cert}")
                all_ok = False
    print("  Spot check done.")

    # Summary
    print(f"\n--- Summary (octaves 0-255) ---")
    for k in range(6):
        vals = [d_data[n][k] for n in range(256)]
        mx = max(vals)
        mi = vals.index(mx)
        print(f"  Max d{k+1}: {mx} at n={mi}")

    # Print d1/lo ratios for a few octaves
    print(f"\n--- d1/lo ratios ---")
    for n in [0, 2, 5, 10, 20, 50, 85, 100, 123, 170, 200, 255]:
        lo = lo_table[n]
        d1 = d_data[n][0]
        if lo > 0:
            print(f"  n={n}: lo={lo}, d1={d1}, d1/lo={d1/lo:.6f}")

    # Verify Sqrt512Cert: fixed-seed certificate for octaves 254/255
    FIXED_SEED = lo_table[255]  # = isqrt(2^255)
    print(f"\n--- Sqrt512Cert verification ---")
    print(f"  FIXED_SEED = {FIXED_SEED}")
    assert FIXED_SEED == hi_table[254], f"FIXED_SEED != hi(254)"
    assert FIXED_SEED == lo_table[255], f"FIXED_SEED != lo(255)"

    for octave in [254, 255]:
        lo = lo_table[octave]
        hi = hi_table[octave]
        ma = compute_maxabs(lo, hi, FIXED_SEED)
        fd1 = compute_d1(lo, hi, FIXED_SEED)
        fd2 = next_d(lo, fd1)
        fd3 = next_d(lo, fd2)
        fd4 = next_d(lo, fd3)
        fd5 = next_d(lo, fd4)
        fd6 = next_d(lo, fd5)
        print(f"  octave {octave}: lo={lo}, hi={hi}, maxAbs={ma}")
        print(f"    fd1={fd1}, fd2={fd2}, fd3={fd3}, fd4={fd4}, fd5={fd5}, fd6={fd6}")
        assert fd6 <= 1, f"fd6 > 1 for octave {octave}!"
        for k, dk in enumerate([fd1, fd2, fd3, fd4, fd5], 1):
            assert dk <= lo, f"fd{k} > lo for octave {octave}!"
        print(f"    All checks pass.")

    # Generate Lean output
    if all_ok:
        generate_lean_file(lo_table, hi_table, d_data, FIXED_SEED, args.output)

    return 0 if all_ok else 1


def generate_lean_file(lo_table, hi_table, d_data, fixed_seed, outpath):
    """Generate the FiniteCert.lean file with SqrtCert and Sqrt512Cert namespaces."""
    print(f"\nGenerating {outpath}...")

    def fmt_array(name, values, comment=""):
        lines = []
        if comment:
            lines.append(f"/-- {comment} -/")
        lines.append(f"def {name} : Array Nat := #[")
        for i, v in enumerate(values):
            comma = "," if i < len(values) - 1 else ""
            lines.append(f"  {v}{comma}")
        lines.append("]")
        return "\n".join(lines)

    # =========================================================================
    # SqrtCert namespace
    # =========================================================================

    content = f"""import Init

/-
  Finite certificate for sqrt upper bound, covering all 256 octaves.

  For each octave i (n = 0..255), the tables provide:
  - loOf(i): lower bound on isqrt(x) for x in [2^i, 2^(i+1)-1]
  - hiOf(i): upper bound on isqrt(x)
  - seedOf(i): the sqrt seed for the octave = 1 <<< ((i+1)/2)
  - maxAbs(i): max(|seed - lo|, |hi - seed|)
  - d1(i): first-step error bound (analytic)
  - nextD, d2..d6: chained error recurrence d^2/(2*lo) + 1

  All 256 octaves verified: d6 <= 1 and dk <= lo for k=1..5.

  Auto-generated by formal/sqrt/generate_sqrt_cert.py — do not edit by hand.
-/

namespace SqrtCert

set_option maxRecDepth 1000000

{fmt_array("loTable", lo_table, "Lower bounds on isqrt(x) for octaves 0..255.")}

{fmt_array("hiTable", hi_table, "Upper bounds on isqrt(x) for octaves 0..255.")}

def seedOf (i : Fin 256) : Nat :=
  1 <<< ((i.val + 1) / 2)

def loOf (i : Fin 256) : Nat :=
  loTable[i.val]!

def hiOf (i : Fin 256) : Nat :=
  hiTable[i.val]!

def maxAbs (i : Fin 256) : Nat :=
  max (seedOf i - loOf i) (hiOf i - seedOf i)

def d1 (i : Fin 256) : Nat :=
  (maxAbs i * maxAbs i + 2 * hiOf i) / (2 * seedOf i)

def nextD (lo d : Nat) : Nat :=
  d * d / (2 * lo) + 1

def d2 (i : Fin 256) : Nat :=
  nextD (loOf i) (d1 i)

def d3 (i : Fin 256) : Nat :=
  nextD (loOf i) (d2 i)

def d4 (i : Fin 256) : Nat :=
  nextD (loOf i) (d3 i)

def d5 (i : Fin 256) : Nat :=
  nextD (loOf i) (d4 i)

def d6 (i : Fin 256) : Nat :=
  nextD (loOf i) (d5 i)

theorem lo_pos : ∀ i : Fin 256, 0 < loOf i := by
  decide

theorem d1_le_lo : ∀ i : Fin 256, d1 i ≤ loOf i := by
  decide

theorem d2_le_lo : ∀ i : Fin 256, d2 i ≤ loOf i := by
  decide

theorem d3_le_lo : ∀ i : Fin 256, d3 i ≤ loOf i := by
  decide

theorem d4_le_lo : ∀ i : Fin 256, d4 i ≤ loOf i := by
  decide

theorem d5_le_lo : ∀ i : Fin 256, d5 i ≤ loOf i := by
  decide

theorem d6_le_one : ∀ i : Fin 256, d6 i ≤ 1 := by
  decide

theorem lo_sq_le_pow2 : ∀ i : Fin 256, loOf i * loOf i ≤ 2 ^ i.val := by
  decide

theorem pow2_succ_le_hi_succ_sq :
    ∀ i : Fin 256, 2 ^ (i.val + 1) ≤ (hiOf i + 1) * (hiOf i + 1) := by
  decide

end SqrtCert

-- ============================================================================
-- Sqrt512Cert: fixed-seed certificates for octaves 254/255
-- Used by the 512-bit sqrt proof (Sqrt512Proof).
-- ============================================================================

namespace Sqrt512Cert

open SqrtCert

/-- The fixed Newton seed used by 512-bit sqrt: isqrt(2^255).
    Equals hiOf(254) = loOf(255) in the finite certificate tables. -/
def FIXED_SEED : Nat := {fixed_seed}

def lo254 : Nat := loOf ⟨254, by omega⟩
def hi254 : Nat := hiOf ⟨254, by omega⟩
def maxAbs254 : Nat := max (FIXED_SEED - lo254) (hi254 - FIXED_SEED)
def fd1_254 : Nat := (maxAbs254 * maxAbs254 + 2 * hi254) / (2 * FIXED_SEED)
def fd2_254 : Nat := nextD lo254 fd1_254
def fd3_254 : Nat := nextD lo254 fd2_254
def fd4_254 : Nat := nextD lo254 fd3_254
def fd5_254 : Nat := nextD lo254 fd4_254
def fd6_254 : Nat := nextD lo254 fd5_254

set_option maxRecDepth 100000 in
theorem fd6_254_le_one : fd6_254 ≤ 1 := by decide
set_option maxRecDepth 100000 in
theorem fd1_254_le_lo : fd1_254 ≤ lo254 := by decide
set_option maxRecDepth 100000 in
theorem fd2_254_le_lo : fd2_254 ≤ lo254 := by decide
set_option maxRecDepth 100000 in
theorem fd3_254_le_lo : fd3_254 ≤ lo254 := by decide
set_option maxRecDepth 100000 in
theorem fd4_254_le_lo : fd4_254 ≤ lo254 := by decide
set_option maxRecDepth 100000 in
theorem fd5_254_le_lo : fd5_254 ≤ lo254 := by decide
theorem lo254_pos : 0 < lo254 := lo_pos ⟨254, by omega⟩

def lo255 : Nat := loOf ⟨255, by omega⟩
def hi255 : Nat := hiOf ⟨255, by omega⟩
def maxAbs255 : Nat := max (FIXED_SEED - lo255) (hi255 - FIXED_SEED)
def fd1_255 : Nat := (maxAbs255 * maxAbs255 + 2 * hi255) / (2 * FIXED_SEED)
def fd2_255 : Nat := nextD lo255 fd1_255
def fd3_255 : Nat := nextD lo255 fd2_255
def fd4_255 : Nat := nextD lo255 fd3_255
def fd5_255 : Nat := nextD lo255 fd4_255
def fd6_255 : Nat := nextD lo255 fd5_255

set_option maxRecDepth 100000 in
theorem fd6_255_le_one : fd6_255 ≤ 1 := by decide
set_option maxRecDepth 100000 in
theorem fd1_255_le_lo : fd1_255 ≤ lo255 := by decide
set_option maxRecDepth 100000 in
theorem fd2_255_le_lo : fd2_255 ≤ lo255 := by decide
set_option maxRecDepth 100000 in
theorem fd3_255_le_lo : fd3_255 ≤ lo255 := by decide
set_option maxRecDepth 100000 in
theorem fd4_255_le_lo : fd4_255 ≤ lo255 := by decide
set_option maxRecDepth 100000 in
theorem fd5_255_le_lo : fd5_255 ≤ lo255 := by decide
theorem lo255_pos : 0 < lo255 := lo_pos ⟨255, by omega⟩

end Sqrt512Cert
"""

    with open(outpath, "w") as f:
        f.write(content)
    print(f"  Written to {outpath}")


if __name__ == "__main__":
    sys.exit(main())
