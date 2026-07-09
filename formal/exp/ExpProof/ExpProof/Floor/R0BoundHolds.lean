import ExpProof.Floor.Fold
import ExpProof.Floor.R0Exp
import ExpProof.Floor.R0ExpUnder
import ExpProof.Seam.RealExp

/-!
# The accumulator-vs-target brackets, discharged

The per-point `r0`-vs-`exp` brackets (`r0_real_over_within`, `r0_real_under_within`) and the
below-clamp bound (`belowC_target_lt_one`) establish the never-over and deficit-under-one facts
about the real pre-floor accumulator unconditionally and axiom-clean, via the octave fold
`E·2^s = WAD·2⁶⁷·exp(rt)` (`WAD·2⁶⁷ = scaleQ67`; `s = 67 − k`, the closing shift; `k ≤ 65` so
`s ≥ 2`).

* `accumReal_over`  ⟸ `r0 ≤ scaleQ67·exp(rt) + (5¹⁸/2⁴¹)·B` and `(5¹⁸/2⁴¹)·B ≤ MARGIN = 1`;
* `accumReal_under` ⟸ `scaleQ67·exp(rt) ≤ r0 + U` (`U = 2993/1000`) and
  `U + MARGIN < 2² ≤ 2^s`.

These make the global floor-or-one-less and one-unit underestimation brackets hypothesis-free.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word
open ExpRealSpec

noncomputable section

set_option maxRecDepth 100000

/-- The accumulator never exceeds the target on the region. -/
theorem accumReal_over (x : Nat) (hx : x < 2 ^ 256) (hC : int256 Cmask < int256 x)
    (hC0 : int256 x < int256 C0thresh) :
    accumReal x ≤ expRayToWadTarget (int256 x) := by
  obtain ⟨s, hsint, hAeq⟩ := accumReal_eq hx hC hC0
  have hps : (0 : Real) < (2 ^ s : Real) := by positivity
  have hfold := target_octave_fold s hsint
  have hover := r0_real_over_within hx hC hC0
  set Ert := Real.exp (reducedArg x) with hErt
  -- r0 − MARGIN ≤ scaleQ67·Ert = E·2^s
  have hbound : (int256 (r0Tree x) : Real) - 1 ≤ expRayToWadTarget (int256 x) * (2 ^ s : Real) := by
    rw [hfold]
    have hwad : (WAD : Real) = (10 ^ 18 : Real) := by unfold WAD; norm_num
    rw [hwad]
    -- (5¹⁸/2⁴¹)·B ≤ 1 = MARGIN
    have hBM : (3814697265625 : Real) * 5737291786393199862 /
        (10000000000000000000 * 2199023255552) ≤ 1 := by norm_num
    linarith [hover, hBM]
  rw [hAeq, div_le_iff₀ hps]
  linarith [hbound]

/-- The target is below the accumulator plus one on the region. -/
theorem accumReal_under (x : Nat) (hx : x < 2 ^ 256) (hC : int256 Cmask < int256 x)
    (hC0 : int256 x < int256 C0thresh) :
    expRayToWadTarget (int256 x) < accumReal x + 1 := by
  obtain ⟨s, hsint, hAeq⟩ := accumReal_eq hx hC hC0
  have hps : (0 : Real) < (2 ^ s : Real) := by positivity
  have hfold := target_octave_fold s hsint
  have hunder := r0_real_under_within hx hC hC0
  obtain ⟨_, hkhi⟩ := kTree_bound hx hC hC0
  set Ert := Real.exp (reducedArg x) with hErt
  -- E·2^s = scaleQ67·Ert < (r0 − MARGIN) + 2^s
  have hbound : expRayToWadTarget (int256 x) * (2 ^ s : Real) <
      ((int256 (r0Tree x) : Real) - 1) + (2 ^ s : Real) := by
    rw [hfold]
    have hwad : (WAD : Real) = (10 ^ 18 : Real) := by unfold WAD; norm_num
    have hs4 : (2 : Int) ≤ (s : Int) := by rw [hsint]; linarith [hkhi]
    have hs4n : 2 ≤ s := by exact_mod_cast hs4
    have hpow : (2 ^ 2 : Real) ≤ (2 ^ s : Real) := pow_le_pow_right₀ (by norm_num) hs4n
    rw [hwad]
    -- U + MARGIN < 2⁴
    have hbudget : (2993 / 1000 : Real) + 1 < (2 ^ 2 : Real) := by
      norm_num
    linarith [hunder, hbudget, hpow]
  -- E < accumReal + 1  ⟺  E·2^s < (r0 − MARGIN) + 2^s
  rw [hAeq]
  have hdiv : ((int256 (r0Tree x) : Real) - 1) / (2 ^ s : Real) + 1 =
      (((int256 (r0Tree x) : Real) - 1) + (2 ^ s : Real)) / (2 ^ s : Real) := by field_simp
  rw [hdiv, lt_div_iff₀ hps]
  linarith [hbound]

/-! ## Hypothesis-free region brackets for the global floor bounds -/

/-- **Floor-or-one-less bracket on the region.** The body result satisfies `r ≤ E ∧ E < r+2`,
discharged from the proven `accumReal_over`/`accumReal_under`. -/
theorem floorOrOneLessBracket_region_uncond {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    FloorOrOneLessBracket (int256 x) (int256 (r1Tree x)) := by
  obtain ⟨hfl, hfl1⟩ := r1Tree_floor_accum hx hC hC0
  exact ExpRealBridge.floorOrOneLessBracket_of_accum hfl hfl1
    (accumReal_over x hx hC hC0) (accumReal_under x hx hC hC0)

end

end ExpYul
