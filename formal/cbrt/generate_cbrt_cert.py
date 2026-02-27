#!/usr/bin/env python3
"""
Generate finite-certificate tables for the cbrt formal proof.

For each of 256 octaves (n = 0..255), where octave n contains x in [2^n, 2^(n+1) - 1]:
  - loOf(n) = icbrt(2^n)           -- lower bound on icbrt(x)
  - hiOf(n) = icbrt(2^(n+1) - 1)  -- upper bound on icbrt(x)
  - seedOf(n) = cbrt seed for octave n
  - d1(n): first-step error bound from algebraic formula
  - d2..d6(n): chained via nextD(lo, d) = d^2/lo + 1

The d1 bound uses the cubic identity:
    3*s^2*(z1 - m) <= (m-s)^2*(m+2s) + 3*m*(m+1)
    <= maxAbs^2*(hi+2s) + 3*hi*(hi+1)
where maxAbs = max(|s-lo|, |hi-s|).

Octaves 0-7 (x < 256) are handled separately by native_decide in Lean.
The certificate covers octaves 8-255 (x >= 256, lo >= 6).
"""

import argparse
import sys


def icbrt(x):
    """Integer cube root (floor)."""
    if x <= 0:
        return 0
    if x < 8:
        return 1
    n = x.bit_length()
    z = 1 << ((n + 2) // 3)
    while True:
        z1 = (2 * z + x // (z * z)) // 3
        if z1 >= z:
            break
        z = z1
    while z * z * z > x:
        z -= 1
    while (z + 1) ** 3 <= x:
        z += 1
    return z


def cbrt_step(x, z):
    """One NR step: floor((floor(x/(z*z)) + 2*z) / 3)"""
    if z == 0:
        return 0
    return (x // (z * z) + 2 * z) // 3


def cbrt_seed(n):
    """Seed for octave n."""
    q = (n + 2) // 3
    return ((0xe9 << q) >> 8) + 1


def next_d(lo, d):
    """Error recurrence: d^2/lo + 1."""
    if lo == 0:
        return d * d + 1
    return d * d // lo + 1


def compute_maxabs(lo, hi, s):
    """max(|s - lo|, |hi - s|)"""
    return max(abs(s - lo), abs(hi - s))


def compute_d1(lo, hi, s):
    """Analytic d1 bound:
    d1 = floor((maxAbs^2*(hi+2s) + 3*hi*(hi+1)) / (3*s^2))
    """
    maxAbs = compute_maxabs(lo, hi, s)
    numerator = maxAbs * maxAbs * (hi + 2 * s) + 3 * hi * (hi + 1)
    denominator = 3 * s * s
    if denominator == 0:
        return 0
    return numerator // denominator


def main():
    parser = argparse.ArgumentParser(
        description="Generate finite-certificate tables for cbrt formal proof"
    )
    parser.add_argument(
        "--output",
        default="CbrtProof/CbrtProof/FiniteCert.lean",
        help="Output Lean file path (default: CbrtProof/CbrtProof/FiniteCert.lean)",
    )
    args = parser.parse_args()

    lo_table = []
    hi_table = []

    for n in range(256):
        lo = icbrt(1 << n)
        hi = icbrt((1 << (n + 1)) - 1)
        lo_table.append(lo)
        hi_table.append(hi)

    # Verify basic properties
    for n in range(256):
        lo = lo_table[n]
        hi = hi_table[n]
        assert lo * lo * lo <= (1 << n), f"lo^3 > 2^n at n={n}"
        assert (1 << (n + 1)) <= (hi + 1) ** 3, f"2^(n+1) > (hi+1)^3 at n={n}"
        assert lo <= hi, f"lo > hi at n={n}"

    # Compute certificate for octaves 8-255
    START_OCTAVE = 8
    all_ok = True
    d_data = {}  # n -> (d1, ..., d6)

    for n in range(START_OCTAVE, 256):
        lo = lo_table[n]
        hi = hi_table[n]
        seed = cbrt_seed(n)

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

        # Check side conditions: 2*dk <= lo for k=1..5
        for k, dk in enumerate([d1, d2, d3, d4, d5], 1):
            if 2 * dk > lo:
                print(f"SIDE FAIL: n={n}, 2*d{k}={2*dk} > lo={lo}")
                all_ok = False

    if all_ok:
        print(f"All octaves {START_OCTAVE}-255 pass: d6 <= 1, all side conditions OK.")
    else:
        print("SOME OCTAVES FAIL.")

    # Exhaustive verification for small octaves to confirm d1 bound
    print(f"\nExhaustive verification of d1 for octaves {START_OCTAVE}-30...")
    for n in range(START_OCTAVE, min(31, 256)):
        lo = lo_table[n]
        hi = hi_table[n]
        seed = cbrt_seed(n)
        d1_cert = d_data[n][0]

        for m in range(lo, hi + 1):
            x_lo_m = max(m * m * m, 1 << n)
            x_hi_m = min((m + 1) ** 3 - 1, (1 << (n + 1)) - 1)
            if x_lo_m > x_hi_m:
                continue
            z1 = cbrt_step(x_hi_m, seed)  # max z1 by mono in x
            actual_d1 = max(0, z1 - m)
            if actual_d1 > d1_cert:
                print(f"  D1 FAIL: n={n}, m={m}, z1={z1}, actual_d1={actual_d1}, cert={d1_cert}")
                all_ok = False
    print("  d1 exhaustive check done.")

    # Spot-check d1 for large octaves (random m values)
    import random
    random.seed(42)
    print("\nSpot-checking d1 for large octaves...")
    for n in range(100, 256, 10):
        lo = lo_table[n]
        hi = hi_table[n]
        seed = cbrt_seed(n)
        d1_cert = d_data[n][0]

        # Test at lo, hi, and random m values
        for m in [lo, hi, lo + (hi - lo) // 3, lo + 2 * (hi - lo) // 3]:
            x_max = min((m + 1) ** 3 - 1, (1 << (n + 1)) - 1)
            x_min = max(m ** 3, 1 << n)
            if x_min > x_max:
                continue
            z1 = cbrt_step(x_max, seed)
            actual_d1 = max(0, z1 - m)
            if actual_d1 > d1_cert:
                print(f"  SPOT FAIL: n={n}, m={m}, z1={z1}, actual_d1={actual_d1}, cert={d1_cert}")
                all_ok = False
    print("  Spot check done.")

    # Also check lo_pos: lo >= 6 for octaves >= 8
    assert all(lo_table[n] >= 6 for n in range(START_OCTAVE, 256)), \
        "lo < 6 for some octave >= 8!"
    print(f"\nAll lo >= 6 for octaves >= {START_OCTAVE}. ✓")

    # Also check 2 <= lo (needed for cbrtStep_upper_of_le)
    assert all(lo_table[n] >= 2 for n in range(START_OCTAVE, 256)), \
        "lo < 2 for some octave >= 8!"

    # Summary
    print(f"\n--- Summary (octaves {START_OCTAVE}-255) ---")
    for k in range(6):
        vals = [d_data[n][k] for n in range(START_OCTAVE, 256)]
        mx = max(vals)
        mi = START_OCTAVE + vals.index(mx)
        print(f"  Max d{k+1}: {mx} at n={mi}")

    # Print d1/lo ratios for a few octaves
    print(f"\n--- d1/lo ratios ---")
    for n in [8, 10, 20, 50, 85, 100, 123, 170, 200, 255]:
        if n >= START_OCTAVE:
            lo = lo_table[n]
            d1 = d_data[n][0]
            print(f"  n={n}: lo={lo}, d1={d1}, d1/lo={d1/lo:.6f}, 2d1/lo={2*d1/lo:.6f}")

    # Generate Lean output
    if all_ok:
        generate_lean_file(lo_table, hi_table, d_data, START_OCTAVE, args.output)

    return 0 if all_ok else 1


def generate_lean_file(lo_table, hi_table, d_data, start_octave, outpath):
    """Generate the CbrtFiniteCert.lean file."""
    print(f"\nGenerating {outpath}...")

    num = 256 - start_octave  # 248 entries

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

    lo_vals = lo_table[start_octave:]
    hi_vals = hi_table[start_octave:]
    seed_vals = [cbrt_seed(n) for n in range(start_octave, 256)]
    d1_vals = [d_data[n][0] for n in range(start_octave, 256)]

    # Compute maxAbs values for the d1 bound proof
    maxabs_vals = [compute_maxabs(lo_table[n], hi_table[n], cbrt_seed(n))
                   for n in range(start_octave, 256)]

    content = f"""import Init

/-
  Finite certificate for cbrt upper bound, covering octaves {start_octave}..255.

  For each octave i (offset from {start_octave}), the tables provide:
  - loOf(i): lower bound on icbrt(x) for x in [2^(i+{start_octave}), 2^(i+{start_octave+1})-1]
  - hiOf(i): upper bound on icbrt(x)
  - seedOf(i): the cbrt seed for the octave
  - maxAbsOf(i): max|seed - m| for m in [lo, hi]
  - d1Of(i): first-step error bound (analytic)
  - nextD, d2..d6: chained error recurrence

  All 248 octaves verified: d6 <= 1 and 2*dk <= lo for k=1..5.
-/

namespace CbrtCert

set_option maxRecDepth 1000000

/-- Offset: certificate octave index i corresponds to bit-length octave i + {start_octave}. -/
def certOffset : Nat := {start_octave}

{fmt_array("loTable", lo_vals, f"Lower bounds on icbrt(x) for octaves {start_octave}..255.")}

{fmt_array("hiTable", hi_vals, f"Upper bounds on icbrt(x) for octaves {start_octave}..255.")}

{fmt_array("seedTable", seed_vals, f"cbrt seed for octaves {start_octave}..255.")}

{fmt_array("maxAbsTable", maxabs_vals, "max(|seed - lo|, |hi - seed|) per octave.")}

{fmt_array("d1Table", d1_vals, "First-step error bound per octave.")}

def loOf (i : Fin {num}) : Nat := loTable[i.val]!
def hiOf (i : Fin {num}) : Nat := hiTable[i.val]!
def seedOf (i : Fin {num}) : Nat := seedTable[i.val]!
def maxAbsOf (i : Fin {num}) : Nat := maxAbsTable[i.val]!
def d1Of (i : Fin {num}) : Nat := d1Table[i.val]!

/-- Error recurrence: d^2/lo + 1. -/
def nextD (lo d : Nat) : Nat := d * d / lo + 1

def d2Of (i : Fin {num}) : Nat := nextD (loOf i) (d1Of i)
def d3Of (i : Fin {num}) : Nat := nextD (loOf i) (d2Of i)
def d4Of (i : Fin {num}) : Nat := nextD (loOf i) (d3Of i)
def d5Of (i : Fin {num}) : Nat := nextD (loOf i) (d4Of i)
def d6Of (i : Fin {num}) : Nat := nextD (loOf i) (d5Of i)

-- ============================================================================
-- Computational verification of certificate properties
-- ============================================================================

/-- lo is always positive. -/
theorem lo_pos : ∀ i : Fin {num}, 0 < loOf i := by decide

/-- lo >= 2 (needed for cbrtStep_upper_of_le). -/
theorem lo_ge_two : ∀ i : Fin {num}, 2 ≤ loOf i := by decide

/-- lo <= hi. -/
theorem lo_le_hi : ∀ i : Fin {num}, loOf i ≤ hiOf i := by decide

/-- seed is positive. -/
theorem seed_pos : ∀ i : Fin {num}, 0 < seedOf i := by decide

/-- lo^3 <= 2^(i + certOffset). -/
theorem lo_cube_le_pow2 : ∀ i : Fin {num},
    loOf i * loOf i * loOf i ≤ 2 ^ (i.val + certOffset) := by native_decide

/-- 2^(i + certOffset + 1) <= (hi+1)^3. -/
theorem pow2_succ_le_hi_succ_cube : ∀ i : Fin {num},
    2 ^ (i.val + certOffset + 1) ≤ (hiOf i + 1) * (hiOf i + 1) * (hiOf i + 1) := by native_decide

/-- d1 is the correct analytic bound:
    d1Of(i) = (maxAbsOf(i)^2 * (hiOf(i) + 2*seedOf(i)) + 3*hiOf(i)*(hiOf(i)+1)) / (3*seedOf(i)^2) -/
theorem d1_eq : ∀ i : Fin {num},
    d1Of i = (maxAbsOf i * maxAbsOf i * (hiOf i + 2 * seedOf i) +
              3 * hiOf i * (hiOf i + 1)) / (3 * (seedOf i * seedOf i)) := by native_decide

/-- maxAbs captures the correct value. -/
theorem maxabs_eq : ∀ i : Fin {num},
    maxAbsOf i = max (seedOf i - loOf i) (hiOf i - seedOf i) := by native_decide

/-- Terminal bound: d6 <= 1 for all certificate octaves. -/
theorem d6_le_one : ∀ i : Fin {num}, d6Of i ≤ 1 := by native_decide

/-- Side condition: 2 * d1 <= lo. -/
theorem two_d1_le_lo : ∀ i : Fin {num}, 2 * d1Of i ≤ loOf i := by native_decide

/-- Side condition: 2 * d2 <= lo. -/
theorem two_d2_le_lo : ∀ i : Fin {num}, 2 * d2Of i ≤ loOf i := by native_decide

/-- Side condition: 2 * d3 <= lo. -/
theorem two_d3_le_lo : ∀ i : Fin {num}, 2 * d3Of i ≤ loOf i := by native_decide

/-- Side condition: 2 * d4 <= lo. -/
theorem two_d4_le_lo : ∀ i : Fin {num}, 2 * d4Of i ≤ loOf i := by native_decide

/-- Side condition: 2 * d5 <= lo. -/
theorem two_d5_le_lo : ∀ i : Fin {num}, 2 * d5Of i ≤ loOf i := by native_decide

/-- Seed matches the cbrt seed formula:
    seedOf(i) = ((0xe9 <<< ((i + certOffset + 2) / 3)) >>> 8) + 1 -/
theorem seed_eq : ∀ i : Fin {num},
    seedOf i = ((0xe9 <<< ((i.val + certOffset + 2) / 3)) >>> 8) + 1 := by native_decide

/-- Perfect-cube key: d5² < lo for all certificate octaves.
    This ensures that on perfect cubes x = m³, the 6th NR step gives exactly m
    (since the per-step error d²/m < 1 when d² < m and m ≥ lo). -/
theorem d5_sq_lt_lo : ∀ i : Fin {num}, d5Of i * d5Of i < loOf i := by native_decide

end CbrtCert
"""

    with open(outpath, "w") as f:
        f.write(content)
    print(f"  Written to {outpath}")


if __name__ == "__main__":
    sys.exit(main())
