import ExpProof.Floor.Fold
import ExpProof.Floor.R0Exp
import ExpProof.Floor.R0ExpUnder
import ExpProof.Seam.RealExp

/-!
# The accumulator-vs-target brackets, discharged

The per-point `r0`-vs-`exp` brackets (`r0_real_over_within`, `r0_real_under_within`) and the
below-clamp bound (`belowC_target_lt_one`) establish the never-over and deficit-under-one facts
about the real pre-floor accumulator unconditionally and axiom-clean, via the octave fold
`E·2^s = WAD·2¹⁰⁸·exp(rt)` (`WAD = 5¹⁸`; `s = 108 − k`, the closing shift; `k ≤ 64` so `s ≥ 44`).

* `accumReal_over`  ⟸ `r0 ≤ 2¹²⁶·exp(rt) + 5792534503673398887/10000000000000000000` and `5¹⁸·5792534503673398887/10000000000000000000 ≤ MARGIN`;
* `accumReal_under` ⟸ `2¹²⁶·exp(rt) ≤ r0 + 31/10` and `(31/10)·5¹⁸ + MARGIN < 2⁴⁵ ≤ 2^s`.

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
  -- WAD·r0 − MARGIN ≤ 5^18·2^126·Ert = E·2^s
  have hbound : (3814697265625 : Real) * (int256 (r0Tree x) : Real) - 2209676553221 ≤
      expRayToWadTarget (int256 x) * (2 ^ s : Real) := by
    rw [hfold]
    have hr0R : (int256 (r0Tree x) : Real) ≤ (2 ^ 126 : Real) * Ert + 5792534503673398887 / 10000000000000000000 := hover
    have hscaled : (3814697265625 : Real) * (int256 (r0Tree x) : Real) ≤
        (3814697265625 : Real) * ((2 ^ 126 : Real) * Ert + 5792534503673398887 / 10000000000000000000) :=
      mul_le_mul_of_nonneg_left hr0R (by norm_num)
    have hwad : (WAD : Real) = (10 ^ 18 : Real) := by unfold WAD; norm_num
    rw [hwad]
    have hconst : (10 ^ 18 : Real) * (2 ^ 108 : Real) * Ert =
        (3814697265625 : Real) * ((2 ^ 126 : Real) * Ert) := by
      rw [show (10 ^ 18 : Real) * (2 ^ 108 : Real) = (3814697265625 : Real) * (2 ^ 126 : Real) from by
        norm_num]
      ring
    rw [hconst]
    -- 5^18·B = 3833775901374.02… ≤ 2209676553221 = MARGIN
    have hBM : (3814697265625 : Real) * (5792534503673398887 / 10000000000000000000) ≤
        2209676553221 := by norm_num
    linarith [hscaled, hBM]
  rw [hAeq, div_le_iff₀ hps]; linarith [hbound]

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
  -- E·2^s = 5^18·2^126·Ert < WAD·r0 − MARGIN + 2^s
  have hbound : expRayToWadTarget (int256 x) * (2 ^ s : Real) <
      ((3814697265625 : Real) * (int256 (r0Tree x) : Real) - 2209676553221) + (2 ^ s : Real) := by
    rw [hfold]
    have hr0R : (2 ^ 126 : Real) * Ert ≤ (int256 (r0Tree x) : Real) + 31 / 10 := hunder
    have hwad : (WAD : Real) = (10 ^ 18 : Real) := by unfold WAD; norm_num
    have hs44 : (44 : Int) ≤ (s : Int) := by rw [hsint]; linarith [hkhi]
    have hs44n : 44 ≤ s := by exact_mod_cast hs44
    have hpow : (2 ^ 44 : Real) ≤ (2 ^ s : Real) := pow_le_pow_right₀ (by norm_num) hs44n
    rw [hwad]
    have hconst : (10 ^ 18 : Real) * (2 ^ 108 : Real) * Ert =
        (3814697265625 : Real) * ((2 ^ 126 : Real) * Ert) := by
      rw [show (10 ^ 18 : Real) * (2 ^ 108 : Real) = (3814697265625 : Real) * (2 ^ 126 : Real) from by
        norm_num]
      ring
    rw [hconst]
    have hscaled : (3814697265625 : Real) * ((2 ^ 126 : Real) * Ert) ≤
        (3814697265625 : Real) * ((int256 (r0Tree x) : Real) + 31 / 10) :=
      mul_le_mul_of_nonneg_left hr0R (by norm_num)
    -- (31/10)·5^18 + MARGIN < 2^44
    have hbudget : (3814697265625 : Real) * (31 / 10) + 2209676553221 < (2 ^ 44 : Real) := by
      norm_num
    linarith [hscaled, hbudget, hpow]
  -- E < accumReal + 1  ⟺  E·2^s < (WAD·r0 − MARGIN) + 2^s
  rw [hAeq]
  have hdiv : ((3814697265625 : Real) * (int256 (r0Tree x) : Real) - 2209676553221) /
      (2 ^ s : Real) + 1 =
      (((3814697265625 : Real) * (int256 (r0Tree x) : Real) - 2209676553221) + (2 ^ s : Real)) /
        (2 ^ s : Real) := by field_simp
  rw [hdiv, lt_div_iff₀ hps]; linarith [hbound]

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
