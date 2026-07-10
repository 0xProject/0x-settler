import ExpProof.Mul.YMono

/-!
# `mulExpRay` joint monotonicity and the octave view of the guard

The joint sign-aware monotonicity composes the two single-argument statements through an
intermediate corner of the rectangle, which is accepted because the headroom shift is antitone
in the magnitude: shrinking the magnitude only grows the accepted exponent set. The mixed-sign
case needs no intermediate — a nonpositive multiplier's result is nonpositive and a nonnegative
multiplier's is nonnegative, directly from the signed bracket's shape.

The guard also admits the octave vocabulary of the natspec: on canonical inputs, rejection is
exactly a too-large magnitude, an exponent at or beyond the unconditional fence, or a live
exponent whose octave count exceeds the headroom shift less two.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open ExpRealSpec

set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

/-! ## Acceptance transfers along the antitone headroom -/

/-- The headroom shift is antitone in the magnitude, including the zero magnitude. -/
theorem scaleShift_antitone' {a b : Nat} (hab : a ≤ b) (hb : b ≤ scaleQ67) :
    scaleShiftTree b ≤ scaleShiftTree a := by
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · subst h0
    rw [scaleShiftTree_zero]
    have hb' : absTree b = b :=
      absTree_nonneg (lt_of_le_of_lt hb (by unfold scaleQ67; norm_num))
    have h := scaleShiftTree_le_127 (y := b) (by rw [hb']; exact hb)
    rw [hb'] at h
    exact h
  · exact scaleShift_antitone hpos hab hb

/-- Shrinking the magnitude keeps an accepted input accepted: the headroom shift only grows. -/
theorem valueDomain_of_abs_le {y1 y2 x : Nat} (hy1 : y1 < 2 ^ 256)
    (h2 : MulExpRayValueDomain y2 x) (hab : absTree y1 ≤ absTree y2) :
    MulExpRayValueDomain y1 x := by
  obtain ⟨⟨hy2, hx⟩, habs2, hxhi, hcase⟩ := h2
  have habs1 : absTree y1 ≤ scaleQ67 := le_trans hab habs2
  refine ⟨⟨hy1, hx⟩, habs1, hxhi, ?_⟩
  by_cases hx0 : int256 x = 0
  · exact Or.inl hx0
  by_cases hcl : int256 x ≤ int256 mulExpRayZeroMax
  · exact Or.inr (Or.inl hcl)
  have hlv2 : 2 ≤ int256 (mulShiftTree y2 x) := by
    rcases hcase with h | h | h
    · exact absurd h hx0
    · exact absurd h hcl
    · exact h
  have hW : WideRegion x := ⟨by omega, hxhi⟩
  refine Or.inr (Or.inr ?_)
  have ht1 := mulShiftTree_transport hy1 hx habs1 hW
  have ht2 := mulShiftTree_transport hy2 hx habs2 hW
  have hanti : scaleShiftTree (absTree y2) ≤ scaleShiftTree (absTree y1) :=
    scaleShift_antitone' hab habs2
  have hantiI : (scaleShiftTree (absTree y2) : Int) ≤ (scaleShiftTree (absTree y1) : Int) := by
    exact_mod_cast hanti
  rw [ht1]
  rw [ht2] at hlv2
  linarith [hantiI, hlv2]

/-! ## Result signs from the bracket shape -/

/-- A nonnegative multiplier's accepted result is nonnegative. -/
theorem mulExpTree_result_nonneg {y x : Nat} (h : MulExpRayValueDomain y x)
    (hyw : y < 2 ^ 255) : 0 ≤ int256 (mulExpTree y x) := by
  obtain ⟨⟨hy, hx⟩, habs, hxhi, hcase⟩ := h
  rcases Nat.eq_zero_or_pos y with h0 | hpos
  · subst h0
    rw [mulExpTree_zero, int256_zero_word']
  by_cases hcl : int256 x ≤ int256 mulExpRayZeroMax
  · rw [mulExpTree_clamped hx hcl, int256_zero_word']
  by_cases hx0 : int256 x = 0
  · have hxz : x = 0 := (int256_zero_iff_of_canonical hx).1 hx0
    subst hxz
    rw [mulExpTree_scale_point hy habs, int256_of_lt hyw]
    exact Int.natCast_nonneg y
  · have hlv : 2 ≤ int256 (mulShiftTree y x) := by
      rcases hcase with h | h | h
      · exact absurd h hx0
      · exact absurd h hcl
      · exact h
    have hW : WideRegion x := ⟨by omega, hxhi⟩
    obtain ⟨hm0, _, _, _⟩ :=
      mulMagnitude_bracket_live hy hx (by omega) habs hx0 hW hlv
    rw [int256_tree_pos hpos hyw]
    exact hm0

/-- A nonpositive multiplier's accepted result is nonpositive. -/
theorem mulExpTree_result_nonpos {y x : Nat} (h : MulExpRayValueDomain y x)
    (hyneg : int256 y ≤ 0) : int256 (mulExpTree y x) ≤ 0 := by
  obtain ⟨⟨hy, hx⟩, habs, hxhi, hcase⟩ := h
  rcases Nat.eq_zero_or_pos y with h0 | hpos
  · subst h0
    rw [mulExpTree_zero, int256_zero_word']
  have hybig : 2 ^ 255 ≤ y := by
    by_contra hsmall
    rw [int256_of_lt (by omega)] at hyneg
    have h1 : y = 0 := by exact_mod_cast le_antisymm (by exact_mod_cast hyneg) (Nat.zero_le y)
    omega
  by_cases hcl : int256 x ≤ int256 mulExpRayZeroMax
  · rw [mulExpTree_clamped hx hcl, int256_zero_word']
  by_cases hx0 : int256 x = 0
  · have hxz : x = 0 := (int256_zero_iff_of_canonical hx).1 hx0
    subst hxz
    rw [mulExpTree_scale_point hy habs]
    exact hyneg
  · have hlv : 2 ≤ int256 (mulShiftTree y x) := by
      rcases hcase with h | h | h
      · exact absurd h hx0
      · exact absurd h hcl
      · exact h
    have hW : WideRegion x := ⟨by omega, hxhi⟩
    obtain ⟨hm0, _, _, _⟩ :=
      mulMagnitude_bracket_live hy hx (by omega) habs hx0 hW hlv
    have hm255 := mag_word_small hy (by omega) hx habs hx0 hW hlv
    rw [int256_tree_neg hybig hy hm255]
    linarith [hm0]

/-! ## The joint statement -/

private theorem tree_of_run {y x r : Nat}
    (hrun : run_mul_exp_ray_evm y x = .ok (mulExpTree y x))
    (hr : run_mul_exp_ray_evm y x = .ok r) : r = mulExpTree y x := by
  rw [hrun] at hr
  injection hr with h
  exact h.symm

/-- **Sign-aware joint monotonicity on the value domain.** For accepted pairs, the results are
ordered when a nonnegative multiplier grows with the exponent, a nonpositive one grows against
it, or the multipliers straddle zero. -/
theorem run_mul_exp_ray_evm_mono_joint {y1 y2 x1 x2 : Nat}
    (h1 : MulExpRayValueDomain y1 x1) (h2 : MulExpRayValueDomain y2 x2)
    (hcond : (0 ≤ int256 y1 ∧ int256 y1 ≤ int256 y2 ∧ int256 x1 ≤ int256 x2) ∨
      (int256 y1 ≤ int256 y2 ∧ int256 y2 ≤ 0 ∧ int256 x2 ≤ int256 x1) ∨
      (int256 y1 ≤ 0 ∧ 0 ≤ int256 y2)) :
    MulExpRayRunJointMonotone y1 y2 x1 x2 := by
  have hrun1 : run_mul_exp_ray_evm y1 x1 = .ok (mulExpTree y1 x1) :=
    run_mul_exp_ray_evm_eq_tree h1
  have hrun2 : run_mul_exp_ray_evm y2 x2 = .ok (mulExpTree y2 x2) :=
    run_mul_exp_ray_evm_eq_tree h2
  refine ⟨mulExpTree y1 x1, mulExpTree y2 x2, hrun1, hrun2, hcond, ?_⟩
  have hy1w : y1 < 2 ^ 256 := h1.1.1
  have hy2w : y2 < 2 ^ 256 := h2.1.1
  rcases hcond with ⟨hy1nn, hy12, hx12⟩ | ⟨hy12, hy2np, hx21⟩ | ⟨hy1np, hy2nn⟩
  · -- both nonnegative, exponents rising: route through (y1, x2)
    have hy1small : y1 < 2 ^ 255 := by
      by_contra hbig
      have := int256_y_neg (by omega) hy1w
      omega
    have hy2small : y2 < 2 ^ 255 := by
      by_contra hbig
      have := int256_y_neg (by omega) hy2w
      omega
    have hab : absTree y1 ≤ absTree y2 := by
      rw [absTree_nonneg hy1small, absTree_nonneg hy2small]
      rw [int256_of_lt hy1small, int256_of_lt hy2small] at hy12
      exact_mod_cast hy12
    have h12 : MulExpRayValueDomain y1 x2 := valueDomain_of_abs_le hy1w h2 hab
    obtain ⟨r1, r2, hr1, hr2, _, hordx⟩ := run_mul_exp_ray_evm_mono_x h1 h12 hx12
    obtain ⟨r3, r4, hr3, hr4, _, hordy⟩ := run_mul_exp_ray_evm_mono_y h12 h2 hy12
    have e1 := tree_of_run hrun1 hr1
    have e2 := tree_of_run (run_mul_exp_ray_evm_eq_tree h12) hr2
    have e3 := tree_of_run (run_mul_exp_ray_evm_eq_tree h12) hr3
    have e4 := tree_of_run hrun2 hr4
    rw [if_neg (int256_y_nonneg hy1small), e1, e2] at hordx
    rw [e3, e4] at hordy
    exact le_trans hordx hordy
  · -- both nonpositive, exponents falling: route through (y2, x1)
    have hab : absTree y2 ≤ absTree y1 := by
      rcases Nat.eq_zero_or_pos y2 with h0 | hpos2
      · subst h0
        rw [show absTree 0 = 0 from absTree_nonneg (by norm_num)]
        exact Nat.zero_le _
      have hy2big : 2 ^ 255 ≤ y2 := by
        by_contra hsmall
        rw [int256_of_lt (by omega)] at hy2np
        have h1 : y2 = 0 := by
          exact_mod_cast le_antisymm (by exact_mod_cast hy2np) (Nat.zero_le y2)
        omega
      have hy1big : 2 ^ 255 ≤ y1 := by
        by_contra hsmall
        have hnn : 0 ≤ int256 y1 := by
          rw [int256_of_lt (by omega)]
          exact Int.natCast_nonneg y1
        have hlt := int256_y_neg hy2big hy2w
        omega
      have ha := int256_neg_eq_abs hy1big hy1w
      have hb := int256_neg_eq_abs hy2big hy2w
      rw [ha, hb] at hy12
      have h1 : (absTree y2 : Int) ≤ (absTree y1 : Int) := by linarith [hy12]
      exact_mod_cast h1
    have h21 : MulExpRayValueDomain y2 x1 := valueDomain_of_abs_le hy2w h1 hab
    obtain ⟨r1, r2, hr1, hr2, _, hordy⟩ := run_mul_exp_ray_evm_mono_y h1 h21 hy12
    obtain ⟨r3, r4, hr3, hr4, _, hordx⟩ := run_mul_exp_ray_evm_mono_x h2 h21 hx21
    have e1 := tree_of_run hrun1 hr1
    have e2 := tree_of_run (run_mul_exp_ray_evm_eq_tree h21) hr2
    have e3 := tree_of_run hrun2 hr3
    have e4 := tree_of_run (run_mul_exp_ray_evm_eq_tree h21) hr4
    rw [e1, e2] at hordy
    rw [e3, e4] at hordx
    -- x-monotonicity at the nonpositive multiplier runs against the exponent
    rcases Nat.eq_zero_or_pos y2 with h0 | hpos2
    · subst h0
      have hz1 : mulExpTree 0 x1 = 0 := mulExpTree_zero x1
      have hz2 : mulExpTree 0 x2 = 0 := mulExpTree_zero x2
      rw [hz1] at hordy
      rw [hz2]
      exact hordy
    · have hy2big : 2 ^ 255 ≤ y2 := by
        by_contra hsmall
        rw [int256_of_lt (by omega)] at hy2np
        have h1 : y2 = 0 := by
          exact_mod_cast le_antisymm (by exact_mod_cast hy2np) (Nat.zero_le y2)
        omega
      rw [if_pos (int256_y_neg hy2big hy2w)] at hordx
      exact le_trans hordy hordx
  · -- straddling zero: nonpositive against nonnegative
    have hy2small : y2 < 2 ^ 255 := by
      by_contra hbig
      have := int256_y_neg (by omega) hy2w
      omega
    have h1np := mulExpTree_result_nonpos h1 hy1np
    have h2nn := mulExpTree_result_nonneg h2 hy2small
    linarith [h1np, h2nn]

/-! ## The octave vocabulary of the guard -/

/-- **The panic domain in octave language.** On canonical inputs, `mulExpRay` rejects exactly a
magnitude above the maximal scale, an exponent at or beyond the unconditional fence, or a live
exponent whose octave count exceeds the headroom shift less two. -/
theorem panicDomain_iff_octave {y x : Nat} (hcanon : MulExpRayCanonical y x) :
    MulExpRayPanicDomain y x ↔
      scaleQ67 < absTree y ∨ int256 mulExpRayHi ≤ int256 x ∨
        (int256 x ≠ 0 ∧ int256 mulExpRayZeroMax < int256 x ∧
          (scaleShiftTree (absTree y) : Int) - 2 < int256 (kTree x)) := by
  obtain ⟨hy, hx⟩ := hcanon
  constructor
  · rintro ⟨_, hbad⟩
    rcases hbad with h | h | ⟨hx0, hzm, hsh⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · by_cases habs : absTree y ≤ scaleQ67
      · by_cases hxhi : int256 x < int256 mulExpRayHi
        · have hW : WideRegion x := ⟨hzm, hxhi⟩
          have ht := mulShiftTree_transport hy hx habs hW
          rw [ht] at hsh
          exact Or.inr (Or.inr ⟨hx0, hzm, by linarith [hsh]⟩)
        · exact Or.inr (Or.inl (by omega))
      · exact Or.inl (by omega)
  · rintro (h | h | ⟨hx0, hzm, hk⟩)
    · exact ⟨⟨hy, hx⟩, Or.inl h⟩
    · exact ⟨⟨hy, hx⟩, Or.inr (Or.inl h)⟩
    · by_cases habs : absTree y ≤ scaleQ67
      · by_cases hxhi : int256 x < int256 mulExpRayHi
        · have hW : WideRegion x := ⟨hzm, hxhi⟩
          have ht := mulShiftTree_transport hy hx habs hW
          refine ⟨⟨hy, hx⟩, Or.inr (Or.inr ⟨hx0, hzm, ?_⟩)⟩
          rw [ht]
          linarith [hk]
        · exact ⟨⟨hy, hx⟩, Or.inr (Or.inl (by omega))⟩
      · exact ⟨⟨hy, hx⟩, Or.inl (by omega)⟩

/-- **The `type(int256).min` multiplier always reverts**: its magnitude word is `2^255`, above
the maximal scale. -/
theorem run_mul_exp_ray_evm_revert_int_min {x : Nat} (hx : x < 2 ^ 256) :
    run_mul_exp_ray_evm (2 ^ 255) x = .error "revert" := by
  apply run_mul_exp_ray_evm_revert
  refine ⟨⟨by norm_num, hx⟩, Or.inl ?_⟩
  rw [absTree_neg (le_refl _) (by norm_num)]
  unfold scaleQ67
  norm_num

end ExpYul
