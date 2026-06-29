import ExpProof.Floor.Fold
import ExpProof.Floor.TBound
import Mathlib.Data.Complex.ExponentialBounds

/-!
# Discharging the runtime `r0` bound

`RuntimeR0Bound` (the single analytic obligation for the public floor brackets) brackets the Q126 quotient
`r0Tree x` against the target `E = 10¹⁸·exp(int256 x / 10²⁷)` across the octave shift `2^(126 − k)`.
This file discharges its self-contained `belowC` field — below the clamp boundary the target is
under one output unit — directly from a `Real.exp` rational bound.

`belowC`: for any word `x` whose signed value is at or below `Cmask = ⌊−18·ln10·10²⁷⌋`, the target
`E = 10¹⁸·exp(int256 x / 10²⁷)` is below `2`. Since `Cmask < −41·10²⁷` and `exp` is increasing,
`E ≤ 10¹⁸·exp(−41)`, and `exp(−41) = (exp 1)⁻⁴¹ < 2·10⁻¹⁸` because `exp 1 > 2.7182818283` (Mathlib's
`Real.exp_one_gt_d9`) forces `(exp 1)⁴¹ > 2.7182818283⁴¹ > 5·10¹⁷`.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open ExpRealSpec
open Real

noncomputable section

set_option maxRecDepth 100000

/-- **Below the clamp boundary the target is under two output units.** For any word `x` whose signed
value is at or below the 0/1 clamp boundary `Cmask`, `E = 10¹⁸·exp(int256 x / 10²⁷) < 2`. -/
theorem belowC_target_lt_two {x : Nat} (hxle : int256 x ≤ int256 Cmask) :
    expRayToWadTarget (int256 x) < 2 := by
  unfold expRayToWadTarget
  have hCm : int256 Cmask = -41446531673892822312323846185 := int256_Cmask
  rw [hCm] at hxle
  have hRAY : (RAY : Real) = 10 ^ 27 := by unfold RAY; norm_num
  have hWAD : (WAD : Real) = 10 ^ 18 := by unfold WAD; norm_num
  have hxR : (int256 x : Real) ≤ -41446531673892822312323846185 := by exact_mod_cast hxle
  -- the reduced argument is at most `−41`
  have harg : (int256 x : Real) / (RAY : Real) ≤ -41 := by
    rw [hRAY, div_le_iff₀ (by norm_num : (0:Real) < 10 ^ 27)]
    nlinarith [hxR]
  have hmono : Real.exp ((int256 x : Real) / (RAY : Real)) ≤ Real.exp (-41) :=
    Real.exp_le_exp.mpr harg
  -- `(exp 1)^41 > 5·10^17` from `exp 1 > 2.7182818283`
  have hexp41 : (5 * 10 ^ 17 : ℝ) < (Real.exp 1) ^ 41 := by
    have h2 : (5 * 10 ^ 17 : ℝ) < (2.7182818283 : ℝ) ^ 41 := by norm_num
    calc (5 * 10 ^ 17 : ℝ) < (2.7182818283 : ℝ) ^ 41 := h2
      _ < (Real.exp 1) ^ 41 := by gcongr; exact Real.exp_one_gt_d9
  have hen : Real.exp (-41) = ((Real.exp 1) ^ 41)⁻¹ := by
    rw [show (-41 : ℝ) = -((41 : ℕ) * (1 : ℝ)) by push_cast; ring, Real.exp_neg, Real.exp_nat_mul]
  have hp : (0 : ℝ) < (Real.exp 1) ^ 41 := by positivity
  have hexpneg41 : Real.exp (-41) < 2 / 10 ^ 18 := by
    rw [hen, inv_lt_iff_one_lt_mul₀ hp, div_mul_eq_mul_div, lt_div_iff₀ (by norm_num : (0:ℝ) < 10 ^ 18)]
    nlinarith [hexp41]
  rw [hWAD]
  calc (10 ^ 18 : ℝ) * Real.exp ((int256 x : Real) / (RAY : Real))
      ≤ 10 ^ 18 * Real.exp (-41) := by
        nlinarith [hmono, Real.exp_pos ((int256 x : Real) / (RAY : Real))]
    _ < 10 ^ 18 * (2 / 10 ^ 18) := by nlinarith [hexpneg41]
    _ = 2 := by norm_num

/-- info: 'ExpYul.belowC_target_lt_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms belowC_target_lt_two

end

end ExpYul
