import ExpProof.Floor.Fold
import ExpProof.Floor.R0Exp

/-!
# Discharging the never-over / deficit / below-clamp fields of `RuntimeR0Bound`

The per-point `r0`-vs-`exp` brackets (`r0_real_over_within`, `r0_real_under_within`) and the
below-clamp bound (`belowC_target_lt_two`) discharge three of the four `RuntimeAccumBound` fields
unconditionally and axiom-clean, via the octave fold `E·2^s = WAD·2¹²⁶·exp(rt)` (`s = 126 − k`, the
closing shift; `k ≤ 63` so `s ≥ 63`).

* `over`  ⟸ `r0 ≤ 2¹²⁶·exp(rt) + 19/25` and `WAD·19/25 ≤ MARGIN`;
* `under` ⟸ `2¹²⁶·exp(rt) ≤ r0 + 8` and `8·WAD + MARGIN < 2⁶³ ≤ 2^s`;
* `belowC` ⟸ `belowC_target_lt_two`.

These make the global floor-or-one-less and one-unit underestimation brackets hypothesis-free
(they consume only `over`/`under`/`belowC`). The central-octave exact-floor bracket additionally
depends on the `centralExactness` obligation.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word
open ExpRealSpec

noncomputable section

set_option maxRecDepth 100000

/-- The accumulator never exceeds the target on the region (`RuntimeAccumBound.over`). -/
theorem accumReal_over (x : Nat) (hx : x < 2 ^ 256) (hC : int256 Cmask < int256 x)
    (hC0 : int256 x < int256 C0thresh) :
    accumReal x ≤ expRayToWadTarget (int256 x) := by
  obtain ⟨s, hsint, hAeq⟩ := accumReal_eq hx hC hC0
  have hps : (0 : Real) < (2 ^ s : Real) := by positivity
  have hfold := target_octave_fold s hsint
  have hover := r0_real_over_within hx hC hC0
  set Ert := Real.exp (reducedArg x) with hErt
  -- WAD·r0 − MARGIN ≤ WAD·2^126·Ert = E·2^s
  have hbound : (10 ^ 18 : Real) * (int256 (r0Tree x) : Real) - 792161285993433738 ≤
      expRayToWadTarget (int256 x) * (2 ^ s : Real) := by
    rw [hfold]
    have hr0R : (int256 (r0Tree x) : Real) ≤ (2 ^ 126 : Real) * Ert + 19 / 25 := hover
    have hscaled : (10 ^ 18 : Real) * (int256 (r0Tree x) : Real) ≤
        (10 ^ 18 : Real) * ((2 ^ 126 : Real) * Ert + 19 / 25) :=
      mul_le_mul_of_nonneg_left hr0R (by norm_num)
    have hwad : (WAD : Real) = (10 ^ 18 : Real) := by unfold WAD; norm_num
    rw [hwad]; nlinarith [hscaled]
  rw [hAeq, div_le_iff₀ hps]; linarith [hbound]

/-- The target is below the accumulator plus one on the region (`RuntimeAccumBound.under`). -/
theorem accumReal_under (x : Nat) (hx : x < 2 ^ 256) (hC : int256 Cmask < int256 x)
    (hC0 : int256 x < int256 C0thresh) :
    expRayToWadTarget (int256 x) < accumReal x + 1 := by
  obtain ⟨s, hsint, hAeq⟩ := accumReal_eq hx hC hC0
  have hps : (0 : Real) < (2 ^ s : Real) := by positivity
  have hfold := target_octave_fold s hsint
  have hunder := r0_real_under_within hx hC hC0
  obtain ⟨_, hkhi⟩ := kTree_bound hx hC hC0
  set Ert := Real.exp (reducedArg x) with hErt
  -- E·2^s = WAD·2^126·Ert < WAD·r0 − MARGIN + 2^s
  have hbound : expRayToWadTarget (int256 x) * (2 ^ s : Real) <
      ((10 ^ 18 : Real) * (int256 (r0Tree x) : Real) - 792161285993433738) + (2 ^ s : Real) := by
    rw [hfold]
    have hr0R : (2 ^ 126 : Real) * Ert ≤ (int256 (r0Tree x) : Real) + 8 := hunder
    have hwad : (WAD : Real) = (10 ^ 18 : Real) := by unfold WAD; norm_num
    have hs63 : (63 : Int) ≤ (s : Int) := by rw [hsint]; linarith [hkhi]
    have hs63n : 63 ≤ s := by exact_mod_cast hs63
    have hpow : (2 ^ 63 : Real) ≤ (2 ^ s : Real) := pow_le_pow_right₀ (by norm_num) hs63n
    rw [hwad]
    have h8wad : (10 ^ 18 : Real) * ((2 ^ 126 : Real) * Ert) ≤
        (10 ^ 18 : Real) * ((int256 (r0Tree x) : Real) + 8) :=
      mul_le_mul_of_nonneg_left (by linarith [hr0R]) (by norm_num)
    have hbudget : (10 ^ 18 : Real) * 8 + 792161285993433738 < (2 ^ 63 : Real) := by norm_num
    nlinarith [h8wad, hbudget, hpow]
  -- E < accumReal + 1  ⟺  E·2^s < (WAD·r0 − MARGIN) + 2^s
  rw [hAeq]
  have hdiv : ((10 ^ 18 : Real) * (int256 (r0Tree x) : Real) - 792161285993433738) /
      (2 ^ s : Real) + 1 =
      (((10 ^ 18 : Real) * (int256 (r0Tree x) : Real) - 792161285993433738) + (2 ^ s : Real)) /
        (2 ^ s : Real) := by field_simp
  rw [hdiv, lt_div_iff₀ hps]; linarith [hbound]

/-! ## Hypothesis-free region brackets for the global floor bounds -/

/-- **Floor-or-one-less bracket on the region.** The body result satisfies `r ≤ E ∧ E < r+2`,
discharged from the proven `accumReal_over`/`accumReal_under` (no `RuntimeAccumBound` hypothesis). -/
theorem floorOrOneLessBracket_region_uncond {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    FloorOrOneLessBracket (int256 x) (int256 (r1Tree x)) := by
  obtain ⟨hfl, hfl1⟩ := r1Tree_floor_accum hx hC hC0
  exact ExpRealBridge.floorOrOneLessBracket_of_accum hfl hfl1
    (accumReal_over x hx hC hC0) (accumReal_under x hx hC hC0)

end

end ExpYul
