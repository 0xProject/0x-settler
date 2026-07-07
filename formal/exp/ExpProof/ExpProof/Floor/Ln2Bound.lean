import Common.Seam.RealExpBridge
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A 235-bit two-sided bound on `Real.log 2`

The runtime reduces `x` by the octave constant `LN2 = ⌊ln2·2²³⁵⌋`
(`= 0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d`). Closing the reduced-argument
real identity (`x/RAY − k·ln2 ≈ t/2¹²⁸`) needs `ln2` pinned to that 235-bit grid:

```
LN2 / 2²³⁵ ≤ ln 2 < (LN2 + 1) / 2²³⁵.
```

Mathlib only provides `ln2` to ten digits (`log_two_lt_d9`/`log_two_gt_d9`), far short of the ~71
digits required. This module certifies both sides through the *same* Taylor-cut machinery the floor
layer uses, with no high-precision Mathlib `log` input:

* `2 ≤ exp((LN2+1)/2²³⁵)` is a depth-49 `capLB` (a single partial sum reaches `2`), giving
  `(LN2+1)/2²³⁵ ≥ ln 2` after `Real.le_log_iff_exp_le`-style reasoning;
* `exp(LN2/2²³⁵) ≤ 2` is a depth-50 `capUB_of_partial` (the geometric tail fits under `2`), giving
  `LN2/2²³⁵ ≤ ln 2`.

Both certificate inequalities are concrete `Nat` comparisons (decided in the kernel), so the bound is
axiom-clean.
-/

namespace ExpYul

open Common.Exp Common.RealExpBridge

noncomputable section

set_option maxRecDepth 100000

/-- The runtime octave constant `LN2 = ⌊ln2·2²³⁵⌋`. -/
def LN2c : Nat := 0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d

/-- The decimal value of `LN2c`. -/
theorem LN2c_eq : LN2c = 38271408169742254668347313025622401492114385419650052359639581444463709 := by
  unfold LN2c; norm_num

/-! ## `exp(LN2/2²³⁵) ≤ 2` via a depth-50 upper cap -/

/-- The upper cut: every Taylor partial sum of `exp(LN2/2²³⁵)` stays at or below `2`. -/
theorem ln2_capUB : capUB LN2c (2 ^ 235) 2 1 := by
  refine capUB_of_partial (by norm_num) (K := 50) ?_ ?_
  · rw [LN2c_eq]; norm_num
  · rw [LN2c_eq]; decide +kernel

/-- `exp(LN2/2²³⁵) ≤ 2`. -/
theorem exp_ln2_le_two : Real.exp ((LN2c : Real) / (2 ^ 235 : Real)) ≤ 2 := by
  have h := exp_le_of_capUB (p := LN2c) (q := 2 ^ 235) (y := 2) (w := 1)
    (by norm_num) (by norm_num) ln2_capUB
  have hq : (((2 ^ 235 : Nat) : Nat) : Real) = (2 ^ 235 : Real) := by
    rw [Nat.cast_pow]; norm_num
  rw [hq] at h
  simpa using h

/-! ## `2 ≤ exp((LN2+1)/2²³⁵)` via a depth-49 lower cap -/

/-- The lower cut: the depth-49 Taylor partial sum of `exp((LN2+1)/2²³⁵)` reaches `2`. -/
theorem ln2_capLB : capLB (LN2c + 1) (2 ^ 235) 2 1 := by
  refine ⟨49, ?_⟩
  rw [LN2c_eq]; decide +kernel

/-- `2 ≤ exp((LN2+1)/2²³⁵)`. -/
theorem two_le_exp_ln2_succ :
    (2 : Real) ≤ Real.exp (((LN2c : Real) + 1) / (2 ^ 235 : Real)) := by
  have h := le_exp_of_capLB (p := LN2c + 1) (q := 2 ^ 235) (y := 2) (w := 1)
    (by norm_num) (by norm_num) ln2_capLB
  have hq : (((2 ^ 235 : Nat) : Nat) : Real) = (2 ^ 235 : Real) := by
    rw [Nat.cast_pow]; norm_num
  have hp : (((LN2c + 1 : Nat) : Real)) = (LN2c : Real) + 1 := by push_cast; ring
  rw [hq, hp] at h
  simpa using h

/-! ## The two-sided `ln 2` bound -/

theorem two_pow_235_pos : (0 : Real) < (2 ^ 235 : Real) := by positivity

/-- **Lower bound:** `LN2/2²³⁵ ≤ ln 2`. From `exp(LN2/2²³⁵) ≤ 2`, applying `Real.log` (monotone) and
`Real.log_exp`. -/
theorem ln2_lower : (LN2c : Real) / (2 ^ 235 : Real) ≤ Real.log 2 := by
  have h := exp_ln2_le_two
  have := Real.log_le_log (Real.exp_pos _) h
  rwa [Real.log_exp] at this

/-- **Upper bound:** `ln 2 < (LN2+1)/2²³⁵`. From `2 ≤ exp((LN2+1)/2²³⁵)` (and strictness off the
boundary, since `LN2 = ⌊ln2·2²³⁵⌋` is strict). -/
theorem ln2_upper : Real.log 2 ≤ ((LN2c : Real) + 1) / (2 ^ 235 : Real) := by
  have h := two_le_exp_ln2_succ
  have := Real.log_le_log (by norm_num : (0:Real) < 2) h
  rwa [Real.log_exp] at this

/-- info: 'ExpYul.ln2_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ln2_lower

/-- info: 'ExpYul.ln2_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ln2_upper

end

end ExpYul
