import ExpProof.Mul.Accum
import ExpProof.Mono.CrossCert
import ExpProof.Mono.Seam

/-!
# `mulExpRay` monotonicity in the exponent

At a fixed multiplier the kernel magnitude is nondecreasing in the exponent over the accepted
inputs. The live region is swept by a unit-step induction: within an octave the scaled quotient is
monotone (the `tod·ev` cross certificate at the dynamic scale), and across a seam the closing
shift loses one bit while the quotient at most doubles three units short
(`r0Scaled_seam_double`), so the shifted floors stay ordered (`seam_close`). The scale point
`x = 0` never sits inside an induction range: a negative live exponent's magnitude is below
`abs(y)` outright (its target is), and a positive live exponent's magnitude is at least `abs(y)`
through the analytic pin step at `x = 1` (`exp(10⁻²⁷) ≥ 1 + 10⁻²⁷` is worth `scale/10²⁷ ≥ 2⁹⁸`
quotient units, far above the deficit envelope). Sign reapplication turns magnitude monotonicity
into the signed public statement on the whole value domain.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word
open ExpRealSpec

set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

/-! ## Word plumbing -/

private theorem int256_inj {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : int256 a = int256 b) : a = b := by
  have hp : (2 : Int) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
    intPow256
  have ha' : (a : Int) < 2 ^ 256 := by exact_mod_cast ha
  have hb' : (b : Int) < 2 ^ 256 := by exact_mod_cast hb
  rw [hp] at ha' hb'
  unfold int256 at h
  split at h <;> split at h <;> first | (rw [hp] at h; omega) | omega

/-- The shift word is constant within an octave (fixed multiplier). -/
private theorem mulShift_word_eq {y x1 x2 : Nat}
    (hk : int256 (kTree x1) = int256 (kTree x2)) :
    mulShiftTree y x1 = mulShiftTree y x2 := by
  have hk1w : kTree x1 < 2 ^ 256 := by unfold kTree; exact evmSar_lt _ _
  have hk2w : kTree x2 < 2 ^ 256 := by unfold kTree; exact evmSar_lt _ _
  unfold mulShiftTree
  rw [int256_inj hk1w hk2w hk]

/-- The signed shift is antitone in the exponent (the octave index is monotone). -/
theorem mulShift_antitone {y x1 x2 : Nat} (hy : y < 2 ^ 256)
    (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (habs : absTree y ≤ scaleQ67) (hW1 : WideRegion x1) (hW2 : WideRegion x2)
    (hle : int256 x1 ≤ int256 x2) :
    int256 (mulShiftTree y x2) ≤ int256 (mulShiftTree y x1) := by
  rw [mulShiftTree_transport hy hx1 habs hW1, mulShiftTree_transport hy hx2 habs hW2]
  have hkmono := kTree_mono_wide hx1 hx2 hW1.1 hle hW2.2
  linarith [hkmono]

/-- The decremented quotient word: transport and range at the dynamic scale. -/
private theorem mulShiftArg_facts {y x : Nat} (hy : y < 2 ^ 256) (hy0 : y ≠ 0)
    (hx : x < 2 ^ 256) (habs : absTree y ≤ scaleQ67) (hW : WideRegion x) :
    int256 (evmSub (r0MulTree y x) marginWord) = int256 (r0MulTree y x) - 1 ∧
      0 ≤ int256 (r0MulTree y x) - 1 ∧ int256 (r0MulTree y x) - 1 < 2 ^ 130 := by
  have hpos : 1 ≤ absTree y := absTree_pos hy hy0
  have hslo : 2 ^ 125 ≤ mulScaleTree y := mulScaleTree_lower hy hpos habs
  obtain ⟨_, _, hshi⟩ := mulScaleTree_spec hy habs
  have hr0eq : r0MulTree y x = r0ScaledTree (mulScaleTree y) x := r0MulTree_eq_scaled y x
  obtain ⟨hr0lo, hr0hi⟩ := r0Scaled_bounds hslo hshi hx hW
  rw [← hr0eq] at hr0lo hr0hi
  have hr0w : r0MulTree y x < 2 ^ 256 := r0MulTree_lt y x
  have hmarlt : (marginWord : Nat) < 2 ^ 256 := by unfold marginWord; norm_num
  have hmari : int256 (marginWord : Nat) = 1 := by
    unfold marginWord
    rw [int256_of_lt (by norm_num)]
    norm_num
  have hp123 : (2:Int)^123 = 10633823966279326983230456482242756608 := by norm_num
  have hp130 : (2:Int)^130 = 1361129467683753853853498429727072845824 := by norm_num
  rw [hp123] at hr0lo
  rw [hp130] at hr0hi
  have hsub : int256 (evmSub (r0MulTree y x) marginWord) = int256 (r0MulTree y x) - 1 := by
    have := evmSub_transport hr0w hmarlt
      (by rw [hmari]; simp only [ipow255]; linarith [hr0lo, hr0hi])
      (by rw [hmari]; simp only [ipow255]; linarith [hr0lo, hr0hi])
    rw [hmari] at this
    exact this
  exact ⟨hsub, by linarith [hr0lo], by linarith [hr0hi]⟩

/-! ## The unit step on the live region -/

/-- Adjacent same-octave quotient monotonicity at the dynamic scale. -/
theorem r0Mul_mono_adjacent {y x1 x2 : Nat} (hy : y < 2 ^ 256)
    (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256) (habs : absTree y ≤ scaleQ67)
    (hW1 : WideRegion x1) (hW2 : WideRegion x2)
    (hk : int256 (kTree x1) = int256 (kTree x2))
    (hadj : int256 x2 = int256 x1 + 1) :
    int256 (r0MulTree y x1) ≤ int256 (r0MulTree y x2) := by
  obtain ⟨_, _, hshi⟩ := mulScaleTree_spec hy habs
  have hv1 : vTree x1 < 2 ^ 120 := (vTree_eq_wide hx1 hW1).2
  have hv2 : vTree x2 < 2 ^ 120 := (vTree_eq_wide hx2 hW2).2
  obtain ⟨hev1lo, hev1hi⟩ := evTree_int hv1
  obtain ⟨hev2lo, hev2hi⟩ := evTree_int hv2
  obtain ⟨htod1lo, htod1hi, _, _⟩ := todTree_bound_wide hx1 hW1
  obtain ⟨htod2lo, htod2hi, _, _⟩ := todTree_bound_wide hx2 hW2
  have hevw1 : evTree x1 < 2 ^ 256 := by unfold evTree; exact evmAdd_lt _ _
  have hevw2 : evTree x2 < 2 ^ 256 := by unfold evTree; exact evmAdd_lt _ _
  have htodw1 : todTree x1 < 2 ^ 256 := by unfold todTree; exact evmSar_lt _ _
  have htodw2 : todTree x2 < 2 ^ 256 := by unfold todTree; exact evmSar_lt _ _
  have hcross := tod_cross_wide hx1 hx2 hW1 hW2 hk hadj
  have hp126 : (2:Int)^126 = 85070591730234615865843651857942052864 := by norm_num
  rw [hp126] at htod1lo htod1hi htod2lo htod2hi
  have hr01 : r0MulTree y x1 =
      evmDiv (evmMul (mulScaleTree y) (evmAdd (evTree x1) (todTree x1)))
        (evmSub (evTree x1) (todTree x1)) := rfl
  have hr02 : r0MulTree y x2 =
      evmDiv (evmMul (mulScaleTree y) (evmAdd (evTree x2) (todTree x2)))
        (evmSub (evTree x2) (todTree x2)) := rfl
  rw [hr01, hr02]
  exact r0_mono_of_cross hshi hevw1 htodw1 hevw2 htodw2 hev1lo hev1hi htod1lo htod1hi
    hev2lo hev2hi htod2lo htod2hi hcross

/-- **The live unit step**: for adjacent live exponents the kernel magnitude is nondecreasing. -/
theorem mulMagnitude_step {y x1 x2 : Nat} (hy : y < 2 ^ 256) (hy0 : y ≠ 0)
    (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256) (habs : absTree y ≤ scaleQ67)
    (hW1 : WideRegion x1) (hW2 : WideRegion x2)
    (hx10 : int256 x1 ≠ 0) (hx20 : int256 x2 ≠ 0)
    (hlive1 : 2 ≤ int256 (mulShiftTree y x1)) (hlive2 : 2 ≤ int256 (mulShiftTree y x2))
    (hadj : int256 x2 = int256 x1 + 1) :
    int256 (mulMagnitudeTree y x1) ≤ int256 (mulMagnitudeTree y x2) := by
  have hm1 := mulMagnitudeTree_live (y := y) hx1 hx10 hW1.1
  have hm2 := mulMagnitudeTree_live (y := y) hx2 hx20 hW2.1
  obtain ⟨harg1eq, harg1nn, harg1hi⟩ := mulShiftArg_facts hy hy0 hx1 habs hW1
  obtain ⟨harg2eq, harg2nn, harg2hi⟩ := mulShiftArg_facts hy hy0 hx2 habs hW2
  obtain ⟨hsh1lo, hsh1lt, hsh1eq⟩ := mulShift_word_facts hy hx1 habs hW1 hlive1
  obtain ⟨hsh2lo, hsh2lt, hsh2eq⟩ := mulShift_word_facts hy hx2 habs hW2 hlive2
  rw [hm1, hm2]
  rcases kTree_step_wide hx1 hx2 hW1 hW2 hadj with hsame | hseam
  · -- same octave: shift words coincide, quotient monotone, same-shift floor monotone
    have hkeq : int256 (kTree x1) = int256 (kTree x2) := hsame.symm
    have hsheq' : mulShiftTree y x1 = mulShiftTree y x2 := mulShift_word_eq hkeq
    have hr0mono := r0Mul_mono_adjacent hy hx1 hx2 habs hW1 hW2 hkeq hadj
    rw [← hsheq']
    set arg1 := evmSub (r0MulTree y x1) marginWord with harg1def
    set arg2 := evmSub (r0MulTree y x2) marginWord with harg2def
    have ha1lt : arg1 < 2 ^ 256 := by rw [harg1def]; exact evmSub_lt _ _
    have ha2lt : arg2 < 2 ^ 256 := by rw [harg2def]; exact evmSub_lt _ _
    clear_value arg1 arg2
    have hargle : int256 arg1 ≤ int256 arg2 := by
      rw [harg1eq, harg2eq]
      exact sub_le_sub_right hr0mono 1
    obtain ⟨he1, hlt1⟩ := int256_eq_of_nonneg ha1lt (by rw [harg1eq]; exact harg1nn)
    obtain ⟨he2, hlt2⟩ := int256_eq_of_nonneg ha2lt (by rw [harg2eq]; exact harg2nn)
    have hargleN : arg1 ≤ arg2 := by
      have : ((arg1 : Nat) : Int) ≤ ((arg2 : Nat) : Int) := by rw [← he1, ← he2]; exact hargle
      exact_mod_cast this
    rw [evmShr_eq_div hsh1lt ha1lt, evmShr_eq_div hsh1lt ha2lt]
    have hqle : arg1 / 2 ^ mulShiftTree y x1 ≤ arg2 / 2 ^ mulShiftTree y x1 :=
      Nat.div_le_div_right hargleN
    have hq1lt : arg1 / 2 ^ mulShiftTree y x1 < 2 ^ 255 := by
      have h1 : arg1 / 2 ^ mulShiftTree y x1 ≤ arg1 := Nat.div_le_self _ _
      exact lt_of_le_of_lt h1 hlt1
    have hq2lt : arg2 / 2 ^ mulShiftTree y x1 < 2 ^ 255 := by
      have h1 : arg2 / 2 ^ mulShiftTree y x1 ≤ arg2 := Nat.div_le_self _ _
      exact lt_of_le_of_lt h1 hlt2
    rw [int256_of_lt hq1lt, int256_of_lt hq2lt]
    exact_mod_cast hqle
  · -- octave seam: shift drops one bit, the quotient at most doubles three units short
    have hpos : 1 ≤ absTree y := absTree_pos hy hy0
    have hslo : 2 ^ 125 ≤ mulScaleTree y := mulScaleTree_lower hy hpos habs
    obtain ⟨_, _, hshi⟩ := mulScaleTree_spec hy habs
    have htr1 := mulShiftTree_transport hy hx1 habs hW1
    have htr2 := mulShiftTree_transport hy hx2 habs hW2
    have hseq : mulShiftTree y x2 + 1 = mulShiftTree y x1 := by
      have h1 : (mulShiftTree y x1 : Int) =
          (scaleShiftTree (absTree y) : Int) - int256 (kTree x1) := by rw [hsh1eq, htr1]
      have h2 : (mulShiftTree y x2 : Int) =
          (scaleShiftTree (absTree y) : Int) - int256 (kTree x2) := by rw [hsh2eq, htr2]
      have : (mulShiftTree y x2 : Int) + 1 = (mulShiftTree y x1 : Int) := by
        rw [h1, h2, hseam]
        ring
      exact_mod_cast this
    have hdouble : int256 (r0MulTree y x1) + 3 ≤ 2 * int256 (r0MulTree y x2) := by
      have h := r0Scaled_seam_double hslo hshi hx1 hx2 hW1 hW2 hseam hadj
      rw [← r0MulTree_eq_scaled, ← r0MulTree_eq_scaled] at h
      exact h
    set arg1 := evmSub (r0MulTree y x1) marginWord with harg1def
    set arg2 := evmSub (r0MulTree y x2) marginWord with harg2def
    have ha1lt : arg1 < 2 ^ 256 := by rw [harg1def]; exact evmSub_lt _ _
    have ha2lt : arg2 < 2 ^ 256 := by rw [harg2def]; exact evmSub_lt _ _
    clear_value arg1 arg2
    have hargle : int256 arg1 ≤ 2 * int256 arg2 := by
      rw [harg1eq, harg2eq]
      linarith [hdouble]
    exact seam_close ha1lt ha2lt hsh1lt hsh2lt hseq
      (by rw [harg1eq]; exact harg1nn) (by rw [harg2eq]; exact harg2nn) hargle

/-! ## The region induction -/

/-- Unit-step induction over the live region: `n` steps up from `x1`, all inside the live region
(the endpoint's live shift bounds every intermediate through octave monotonicity, and the sign
condition keeps the scale point outside the range). -/
theorem mulMagnitude_mono_steps {y : Nat} (hy : y < 2 ^ 256) (hy0 : y ≠ 0)
    (habs : absTree y ≤ scaleQ67) (n : Nat) :
    ∀ x1 : Nat, x1 < 2 ^ 256 →
    int256 mulExpRayZeroMax < int256 x1 →
    int256 x1 + n < int256 mulExpRayHi →
    (int256 x1 + n < 0 ∨ 0 < int256 x1) →
    2 ≤ int256 (mulShiftTree y (uint256OfInt (int256 x1 + n))) →
    int256 x1 + n = int256 (uint256OfInt (int256 x1 + n)) →
    int256 (mulMagnitudeTree y x1) ≤
      int256 (mulMagnitudeTree y (uint256OfInt (int256 x1 + n))) := by
  induction n with
  | zero =>
    intro x1 hx1 hlo _ _ _ _
    have hw : uint256OfInt (int256 x1 + (0 : Nat)) = x1 := by
      rw [show ((0 : Nat) : Int) = 0 by rfl, Int.add_zero]
      exact uint256OfInt_int256 hx1
    rw [hw]
  | succ m ih =>
    intro x1 hx1 hlo hbnd hsign hlive htgt
    obtain ⟨hzm, hhi⟩ : int256 mulExpRayZeroMax < int256 x1 + 1 ∧
        int256 x1 + 1 < int256 mulExpRayHi := by
      have h1 : int256 x1 + (m + 1 : Nat) < int256 mulExpRayHi := hbnd
      push_cast at h1
      omega
    have hw1lt : uint256OfInt (int256 x1 + 1) < 2 ^ 256 := uint256OfInt_lt _
    have hw1eq : int256 (uint256OfInt (int256 x1 + 1)) = int256 x1 + 1 := by
      refine int256_uint256OfInt ?_ ?_
      · rw [int256_mulExpRayZeroMax] at hzm
        simp only [ipow255]
        omega
      · rw [int256_mulExpRayHi] at hhi
        simp only [ipow255]
        omega
    set x' := uint256OfInt (int256 x1 + 1) with hx'
    have hW1 : WideRegion x1 := ⟨hlo, by
      have h1 : int256 x1 + (m + 1 : Nat) < int256 mulExpRayHi := hbnd
      push_cast at h1
      omega⟩
    have hW' : WideRegion x' := ⟨by omega, by omega⟩
    -- the top endpoint of the range
    set xt := uint256OfInt (int256 x1 + (m + 1 : Nat)) with hxt
    have hxtlt : xt < 2 ^ 256 := uint256OfInt_lt _
    have hWt : WideRegion xt := by
      constructor
      · rw [← htgt]
        push_cast
        omega
      · rw [← htgt]
        exact hbnd
    -- every point below the top endpoint keeps at least its shift
    have hlive' : 2 ≤ int256 (mulShiftTree y x') := by
      have hmono := mulShift_antitone hy hw1lt hxtlt habs hW' hWt (by
        rw [hw1eq, ← htgt]
        push_cast
        omega)
      linarith [hmono, hlive]
    have hlive1 : 2 ≤ int256 (mulShiftTree y x1) := by
      have hmono := mulShift_antitone hy hx1 hxtlt habs hW1 hWt (by
        rw [← htgt]
        push_cast
        omega)
      linarith [hmono, hlive]
    -- the scale point stays outside the range
    have hx10 : int256 x1 ≠ 0 := by
      rcases hsign with h | h
      · push_cast at h
        omega
      · omega
    have hx'0 : int256 x' ≠ 0 := by
      rw [hw1eq]
      rcases hsign with h | h
      · push_cast at h
        omega
      · omega
    have hstep : int256 (mulMagnitudeTree y x1) ≤ int256 (mulMagnitudeTree y x') :=
      mulMagnitude_step hy hy0 hx1 hw1lt habs hW1 hW' hx10 hx'0 hlive1 hlive' hw1eq
    -- the remaining `m` steps from `x'`
    have hsum : int256 x' + (m : Int) = int256 x1 + (m + 1 : Nat) := by
      rw [hw1eq]
      push_cast
      ring
    have hrec := ih x' hw1lt (by omega) (by rw [hsum]; exact hbnd)
      (by
        rcases hsign with h | h
        · left
          rw [hsum]
          push_cast at h ⊢
          omega
        · right
          rw [hw1eq]
          omega)
      (by rw [hsum]; exact hlive)
      (by rw [hsum]; exact htgt)
    rw [hsum] at hrec
    calc int256 (mulMagnitudeTree y x1) ≤ int256 (mulMagnitudeTree y x') := hstep
      _ ≤ int256 (mulMagnitudeTree y (uint256OfInt (int256 x1 + (m + 1 : Nat)))) := hrec

/-- **Region monotonicity of the live magnitude**: for live exponents `x1 ≤ x2` on a common sign
side, the kernel magnitude is nondecreasing. -/
theorem mulMagnitude_region_mono {y x1 x2 : Nat} (hy : y < 2 ^ 256) (hy0 : y ≠ 0)
    (habs : absTree y ≤ scaleQ67)
    (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hW1 : WideRegion x1) (hW2 : WideRegion x2)
    (hle : int256 x1 ≤ int256 x2)
    (hsign : int256 x2 < 0 ∨ 0 < int256 x1)
    (hlive2 : 2 ≤ int256 (mulShiftTree y x2)) :
    int256 (mulMagnitudeTree y x1) ≤ int256 (mulMagnitudeTree y x2) := by
  set n := (int256 x2 - int256 x1).toNat with hn
  have hnval : (n : Int) = int256 x2 - int256 x1 := by
    rw [hn]
    exact Int.toNat_of_nonneg (by omega)
  have hx2eq : int256 x1 + (n : Int) = int256 x2 := by rw [hnval]; ring
  have hcanon : uint256OfInt (int256 x1 + (n : Int)) = x2 := by
    rw [hx2eq]
    exact uint256OfInt_int256 hx2
  have h := mulMagnitude_mono_steps hy hy0 habs n x1 hx1 hW1.1
    (by rw [hx2eq]; exact hW2.2)
    (by
      rcases hsign with h | h
      · left
        rw [hx2eq]
        exact h
      · right
        exact h)
    (by rw [hcanon]; exact hlive2)
    (by rw [hcanon, hx2eq])
  rw [hcanon] at h
  exact h

/-! ## The scale-point comparisons -/

/-- The octave index at `x = 1` is zero. -/
private theorem kTree_one : int256 (kTree 1) = 0 := by
  have hW : WideRegion 1 := by
    constructor
    · rw [int256_mulExpRayZeroMax, int256_of_lt (by norm_num : (1:Nat) < 2 ^ 255)]
      norm_num
    · rw [int256_mulExpRayHi, int256_of_lt (by norm_num : (1:Nat) < 2 ^ 255)]
      norm_num
  obtain ⟨hlo, hhi⟩ := kTree_sandwich_wide (by norm_num) hW
  rw [int256_of_lt (by norm_num : (1:Nat) < 2 ^ 255)] at hlo hhi
  have hcinv : (0x724d54edbacbebbb95c52a0f60 : Int) = 9055943544797870567083544809312 := by
    norm_num
  rw [hcinv] at hlo hhi
  have p199 : (2 : Int) ^ 191 =
      3138550867693340381917894711603833208051177722232017256448 := by norm_num
  have p200 : (2 : Int) ^ 192 =
      6277101735386680763835789423207666416102355444464034512896 := by norm_num
  rw [p199, p200] at hlo hhi
  set k := int256 (kTree 1) with hk
  clear_value k
  omega

/-- The magnitude at the scale point is the multiplier's magnitude. -/
private theorem int256_mulMagnitude_zero {y : Nat} (hy : y < 2 ^ 256) (hy0 : y ≠ 0)
    (habs : absTree y ≤ scaleQ67) :
    int256 (mulMagnitudeTree y 0) = (absTree y : Int) := by
  have hpos : 0 < absTree y := absTree_pos hy hy0
  rw [mulMagnitudeTree_scale_point hy hpos habs]
  exact int256_of_lt (lt_of_le_of_lt habs (by unfold scaleQ67; norm_num))

/-- **The analytic pin step.** At `x = 1` the live magnitude is at least the multiplier's
magnitude: one exponent unit is worth `scale/10²⁷ ≥ 2⁹⁸` quotient units, far above the deficit
envelope, so the decremented quotient still clears `scale` and its closing shift clears
`abs(y)`. -/
theorem mulMagnitude_pin_step {y : Nat} (hy : y < 2 ^ 256) (hy0 : y ≠ 0)
    (habs : absTree y ≤ scaleQ67)
    (hlive1 : 2 ≤ int256 (mulShiftTree y 1)) :
    (absTree y : Int) ≤ int256 (mulMagnitudeTree y 1) := by
  have hx1 : (1 : Nat) < 2 ^ 256 := by norm_num
  have hW : WideRegion 1 := by
    constructor
    · rw [int256_mulExpRayZeroMax, int256_of_lt (by norm_num : (1:Nat) < 2 ^ 255)]
      norm_num
    · rw [int256_mulExpRayHi, int256_of_lt (by norm_num : (1:Nat) < 2 ^ 255)]
      norm_num
  have hi1 : int256 (1 : Nat) = 1 := by
    rw [int256_of_lt (by norm_num : (1:Nat) < 2 ^ 255)]
    norm_num
  have hpos : 1 ≤ absTree y := absTree_pos hy hy0
  have hslo : 2 ^ 125 ≤ mulScaleTree y := mulScaleTree_lower hy hpos habs
  obtain ⟨hs256, hscale_eq, hshi⟩ := mulScaleTree_spec hy habs
  have hunder := r0Scaled_real_under_within (scale := mulScaleTree y) hslo hshi hx1 hW
  have hr0eqM : r0ScaledTree (mulScaleTree y) 1 = r0MulTree y 1 := (r0MulTree_eq_scaled y 1).symm
  rw [hr0eqM] at hunder
  have hm := mulMagnitudeTree_live (y := y) hx1 (by rw [hi1]; norm_num) (by
    rw [int256_mulExpRayZeroMax, hi1]
    norm_num)
  obtain ⟨hargeq, hargnn, harghi⟩ := mulShiftArg_facts hy hy0 hx1 habs hW
  obtain ⟨hshlo, hshlt, hsheq⟩ := mulShift_word_facts hy hx1 habs hW hlive1
  have htr := mulShiftTree_transport hy hx1 habs hW
  have hshS : mulShiftTree y 1 = scaleShiftTree (absTree y) := by
    have h1 : (mulShiftTree y 1 : Int) = (scaleShiftTree (absTree y) : Int) := by
      rw [hsheq, htr, kTree_one]
      ring
    exact_mod_cast h1
  rw [hm, hshS]
  -- every deep word becomes an opaque name before the arithmetic
  set r0w := r0MulTree y 1 with hr0w_def
  have hr0wlt : r0w < 2 ^ 256 := by rw [hr0w_def]; exact r0MulTree_lt y 1
  clear_value r0w
  set sc := mulScaleTree y with hsc_def
  clear_value sc
  set ay := absTree y with hay_def
  set S := scaleShiftTree ay with hS_def
  clear_value S
  clear_value ay
  -- the quotient clears the scale by at least two units
  have hred : reducedArg 1 = 1 / (10 ^ 27 : Real) := by
    unfold reducedArg
    rw [hi1, kTree_one]
    push_cast
    ring
  have hexp1 : (1 : Real) + 1 / (10 ^ 27 : Real) ≤ Real.exp (reducedArg 1) := by
    rw [hred]
    have := Real.add_one_le_exp (1 / (10 ^ 27 : Real))
    linarith [this]
  have hscaleR : (2:Real) ^ 125 ≤ ((sc : Nat) : Real) := by exact_mod_cast hslo
  have hscale_nn : (0:Real) ≤ ((sc : Nat) : Real) := Nat.cast_nonneg sc
  have hgain : ((sc : Nat) : Real) + 5 ≤ ((sc : Nat) : Real) * Real.exp (reducedArg 1) := by
    have h1 : ((sc : Nat) : Real) * ((1 : Real) + 1 / (10 ^ 27 : Real)) ≤
        ((sc : Nat) : Real) * Real.exp (reducedArg 1) :=
      mul_le_mul_of_nonneg_left hexp1 hscale_nn
    have h2 : (5:Real) ≤ ((sc : Nat) : Real) * (1 / (10 ^ 27 : Real)) := by
      have h3 : (5:Real) ≤ ((2:Real) ^ 125) * (1 / (10 ^ 27 : Real)) := by norm_num
      have h4 : ((2:Real) ^ 125) * (1 / (10 ^ 27 : Real)) ≤
          ((sc : Nat) : Real) * (1 / (10 ^ 27 : Real)) :=
        mul_le_mul_of_nonneg_right hscaleR (by positivity)
      linarith [h3, h4]
    have hdistrib : ((sc : Nat) : Real) * ((1 : Real) + 1 / (10 ^ 27 : Real)) =
        ((sc : Nat) : Real) + ((sc : Nat) : Real) * (1 / (10 ^ 27 : Real)) := by ring
    linarith [h1, h2, hdistrib]
  have hq2 : ((sc : Nat) : Real) + 2 ≤ (int256 r0w : Real) := by
    linarith [hunder, hgain]
  have hq2I : ((sc : Nat) : Int) + 2 ≤ int256 r0w := by
    have h : (((sc : Nat) : Int) + 2 : Real) ≤ ((int256 r0w : Int) : Real) := by
      push_cast
      linarith [hq2]
    exact_mod_cast h
  -- word-level: the shifted decremented quotient clears the magnitude
  set arg := evmSub r0w marginWord with hargdef
  have halt : arg < 2 ^ 256 := by rw [hargdef]; exact evmSub_lt _ _
  clear_value arg
  obtain ⟨hae, halt255⟩ := int256_eq_of_nonneg halt (by rw [hargeq]; exact hargnn)
  have hargN : sc + 1 ≤ arg := by
    have h1 : ((sc + 1 : Nat) : Int) ≤ ((arg : Nat) : Int) := by
      rw [← hae, hargeq]
      push_cast
      linarith [hq2I]
    exact_mod_cast h1
  rw [evmShr_eq_div hs256 halt]
  have hdiv : ay ≤ arg / 2 ^ S := by
    rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _)]
    calc ay * 2 ^ S = sc := hscale_eq.symm
      _ ≤ arg := le_trans (Nat.le_add_right _ 1) hargN
  have hqlt : arg / 2 ^ S < 2 ^ 255 := by
    have h1 : arg / 2 ^ S ≤ arg := Nat.div_le_self _ _
    exact lt_of_le_of_lt h1 halt255
  rw [int256_of_lt hqlt]
  exact_mod_cast hdiv

/-- A negative live exponent's magnitude never exceeds the multiplier's magnitude: its real
target is already below it. -/
theorem mulMagnitude_le_abs_of_neg {y x : Nat} (hy : y < 2 ^ 256) (hy0 : y ≠ 0)
    (hx : x < 2 ^ 256) (habs : absTree y ≤ scaleQ67)
    (hW : WideRegion x) (hxneg : int256 x < 0)
    (hlive : 2 ≤ int256 (mulShiftTree y x)) :
    int256 (mulMagnitudeTree y x) ≤ (absTree y : Int) := by
  obtain ⟨hm0, _, hmle, _⟩ := mulMagnitude_bracket_live hy hx hy0 habs (by omega) hW hlive
  have hAlt : mulExpRayMagnitudeTarget (int256 y) (int256 x) < ((absTree y : Nat) : Real) := by
    unfold mulExpRayMagnitudeTarget
    have hay : ((int256 y).natAbs : Real) = ((absTree y : Nat) : Real) := by
      rw [absTree_eq_natAbs hy]
    rw [hay]
    have hexplt : Real.exp ((int256 x : Real) / ((RAY : Nat) : Real)) < 1 := by
      apply Real.exp_lt_one_iff.mpr
      apply div_neg_of_neg_of_pos
      · exact_mod_cast hxneg
      · have : ((RAY : Nat) : Real) = (10 ^ 27 : Real) := by unfold RAY; push_cast; norm_num
        rw [this]
        positivity
    have hpos : (0:Real) < ((absTree y : Nat) : Real) := by
      have h1 : 1 ≤ absTree y := absTree_pos hy hy0
      exact_mod_cast h1
    have h5 := mul_lt_mul_of_pos_left hexplt hpos
    rw [mul_one] at h5
    exact h5
  have h1 : (int256 (mulMagnitudeTree y x) : Real) < ((absTree y : Nat) : Real) :=
    lt_of_le_of_lt hmle hAlt
  have h2 : int256 (mulMagnitudeTree y x) < ((absTree y : Nat) : Int) := by exact_mod_cast h1
  exact le_of_lt h2

/-! ## Sign transports -/

private theorem int256_zero_word' : int256 (0 : Nat) = 0 := by unfold int256; norm_num

private theorem int256_pos_eq_abs {y : Nat} (hneg : y < 2 ^ 255) :
    int256 y = (absTree y : Int) := by
  rw [absTree_nonneg hneg, int256_of_lt hneg]

private theorem int256_neg_eq_abs {y : Nat} (hlo : 2 ^ 255 ≤ y) (hy : y < 2 ^ 256) :
    int256 y = -(absTree y : Int) := by
  rw [absTree_neg hlo hy]
  unfold int256
  rw [if_neg (by omega)]
  omega

private theorem int256_y_neg {y : Nat} (hlo : 2 ^ 255 ≤ y) (hy : y < 2 ^ 256) :
    int256 y < 0 := by
  unfold int256
  rw [if_neg (by omega)]
  have h1 : (y : Int) < 2 ^ 256 := by exact_mod_cast hy
  omega

private theorem int256_y_nonneg {y : Nat} (hneg : y < 2 ^ 255) :
    ¬ (int256 y < 0) := by
  rw [int256_of_lt hneg]
  exact not_lt.mpr (Int.natCast_nonneg y)

/-- The signed tree result under a positive multiplier is the magnitude. -/
private theorem int256_tree_pos {y x : Nat} (hpos : 0 < y) (hneg : y < 2 ^ 255) :
    int256 (mulExpTree y x) = int256 (mulMagnitudeTree y x) := by
  rw [mulExpTree_pos hpos hneg]

/-- The signed tree result under a negative multiplier is the negated magnitude. -/
private theorem int256_tree_neg {y x : Nat} (hlo : 2 ^ 255 ≤ y) (hy : y < 2 ^ 256)
    (hm255 : mulMagnitudeTree y x < 2 ^ 255) :
    int256 (mulExpTree y x) = -(int256 (mulMagnitudeTree y x)) := by
  rcases Nat.eq_zero_or_pos (mulMagnitudeTree y x) with hmz | hmpos
  · have hzero : mulExpTree y x = 0 := by
      unfold mulExpTree
      rw [hmz]
      unfold evmMul
      rw [u256_of_lt_pow256 (by norm_num : (0:Nat) < 2 ^ 256)]
      simp [u256, WORD_MOD]
    rw [hzero, hmz, int256_zero_word']
    norm_num
  · rw [mulExpTree_negative hlo hy hmpos]
    have hres : int256 (2 ^ 256 - mulMagnitudeTree y x) = -(int256 (mulMagnitudeTree y x)) := by
      unfold int256
      rw [if_neg (by omega), if_pos hm255]
      omega
    exact hres

/-- The live magnitude word stays below `2^255`. -/
private theorem mag_word_small {y x : Nat} (hy : y < 2 ^ 256) (hy0 : y ≠ 0)
    (hx : x < 2 ^ 256) (habs : absTree y ≤ scaleQ67)
    (hx0 : int256 x ≠ 0) (hW : WideRegion x)
    (hlive : 2 ≤ int256 (mulShiftTree y x)) :
    mulMagnitudeTree y x < 2 ^ 255 := by
  obtain ⟨hm0, hmlt, _, _⟩ := mulMagnitude_bracket_live hy hx hy0 habs hx0 hW hlive
  obtain ⟨hmi, _⟩ := int256_eq_of_nonneg (mulMagnitudeTree_lt y x) hm0
  have h : ((mulMagnitudeTree y x : Nat) : Int) < 2 ^ 128 := by rw [← hmi]; exact hmlt
  have h' : mulMagnitudeTree y x < 2 ^ 128 := by exact_mod_cast h
  have : (2:Nat) ^ 128 < 2 ^ 255 := by norm_num
  omega

/-! ## Magnitude monotonicity over the live region -/

/-- A positive live exponent's magnitude is at least the multiplier's magnitude (through the
analytic pin step at `x = 1`). -/
theorem mulMagnitude_ge_abs_of_pos {y x : Nat} (hy : y < 2 ^ 256) (hy0 : y ≠ 0)
    (hx : x < 2 ^ 256) (habs : absTree y ≤ scaleQ67)
    (hW : WideRegion x) (hxpos : 0 < int256 x)
    (hlive : 2 ≤ int256 (mulShiftTree y x)) :
    (absTree y : Int) ≤ int256 (mulMagnitudeTree y x) := by
  have hW1 : WideRegion 1 := by
    constructor
    · rw [int256_mulExpRayZeroMax, int256_of_lt (by norm_num : (1:Nat) < 2 ^ 255)]
      norm_num
    · rw [int256_mulExpRayHi, int256_of_lt (by norm_num : (1:Nat) < 2 ^ 255)]
      norm_num
  have hi1 : int256 (1 : Nat) = 1 := by
    rw [int256_of_lt (by norm_num : (1:Nat) < 2 ^ 255)]
    norm_num
  have h1le : int256 (1 : Nat) ≤ int256 x := by
    rw [hi1]
    omega
  have hsh1 : 2 ≤ int256 (mulShiftTree y 1) := by
    have h := mulShift_antitone hy (by norm_num) hx habs hW1 hW h1le
    linarith [h, hlive]
  have hpin := mulMagnitude_pin_step hy hy0 habs hsh1
  have hmono := mulMagnitude_region_mono hy hy0 habs (by norm_num) hx hW1 hW h1le
    (Or.inr (by rw [hi1]; norm_num)) hlive
  linarith [hpin, hmono]

/-- **Magnitude monotonicity over the live region**, both sign sides, through the scale point. -/
theorem mulMagnitude_mono_pair {y x1 x2 : Nat} (hy : y < 2 ^ 256) (hy0 : y ≠ 0)
    (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256) (habs : absTree y ≤ scaleQ67)
    (hW1 : WideRegion x1) (hW2 : WideRegion x2)
    (hx10 : int256 x1 ≠ 0) (hx20 : int256 x2 ≠ 0)
    (hlive1 : 2 ≤ int256 (mulShiftTree y x1)) (hlive2 : 2 ≤ int256 (mulShiftTree y x2))
    (hle : int256 x1 ≤ int256 x2) :
    int256 (mulMagnitudeTree y x1) ≤ int256 (mulMagnitudeTree y x2) := by
  rcases lt_or_gt_of_ne hx20 with hx2neg | hx2pos
  · -- both negative: one sign side
    exact mulMagnitude_region_mono hy hy0 habs hx1 hx2 hW1 hW2 hle (Or.inl hx2neg) hlive2
  · rcases lt_or_gt_of_ne hx10 with hx1neg | hx1pos
    · -- crossing the scale point: below it the magnitude is under `abs(y)`, above it at least
      calc int256 (mulMagnitudeTree y x1)
          ≤ (absTree y : Int) := mulMagnitude_le_abs_of_neg hy hy0 hx1 habs hW1 hx1neg hlive1
        _ ≤ int256 (mulMagnitudeTree y x2) :=
            mulMagnitude_ge_abs_of_pos hy hy0 hx2 habs hW2 hx2pos hlive2
    · -- both positive: one sign side
      exact mulMagnitude_region_mono hy hy0 habs hx1 hx2 hW1 hW2 hle (Or.inr hx1pos) hlive2

/-! ## The public runtime statement -/

/-- **Monotonicity in the exponent on the value domain.** For a fixed multiplier and accepted
exponents `x1 ≤ x2`, the signed results are ordered along the multiplier's sign. -/
theorem run_mul_exp_ray_evm_mono_x {y x1 x2 : Nat}
    (h1 : MulExpRayValueDomain y x1) (h2 : MulExpRayValueDomain y x2)
    (hle : int256 x1 ≤ int256 x2) :
    MulExpRayRunMonotone y x1 x2 := by
  obtain ⟨⟨hy, hx1w⟩, habs1, hxhi1, hcase1⟩ := h1
  obtain ⟨⟨_, hx2w⟩, habs2, hxhi2, hcase2⟩ := h2
  have hrun1 : run_mul_exp_ray_evm y x1 = .ok (mulExpTree y x1) :=
    run_mul_exp_ray_evm_eq_tree ⟨⟨hy, hx1w⟩, habs1, hxhi1, hcase1⟩
  have hrun2 : run_mul_exp_ray_evm y x2 = .ok (mulExpTree y x2) :=
    run_mul_exp_ray_evm_eq_tree ⟨⟨hy, hx2w⟩, habs2, hxhi2, hcase2⟩
  refine ⟨mulExpTree y x1, mulExpTree y x2, hrun1, hrun2, hle, ?_⟩
  rcases Nat.eq_zero_or_pos y with hy0 | hypos
  · subst hy0
    rw [mulExpTree_zero, mulExpTree_zero, int256_zero_word']
    split <;> exact le_refl 0
  have hy0 : y ≠ 0 := Nat.pos_iff_ne_zero.mp hypos
  -- the signed magnitude of each accepted result
  have habs := habs1
  -- classify each exponent: clamp, scale point, or live
  have hclass : ∀ x : Nat, x < 2 ^ 256 → int256 x < int256 mulExpRayHi →
      (int256 x = 0 ∨ int256 x ≤ int256 mulExpRayZeroMax ∨ 2 ≤ int256 (mulShiftTree y x)) →
      int256 x ≤ int256 mulExpRayZeroMax ∨ x = 0 ∨
        (int256 mulExpRayZeroMax < int256 x ∧ int256 x ≠ 0 ∧
          2 ≤ int256 (mulShiftTree y x)) := by
    intro x hxw hxhi hcase
    by_cases hcl : int256 x ≤ int256 mulExpRayZeroMax
    · exact Or.inl hcl
    by_cases hx0 : int256 x = 0
    · exact Or.inr (Or.inl ((int256_zero_iff_of_canonical hxw).1 hx0))
    · rcases hcase with h | h | h
      · exact absurd h hx0
      · exact absurd h hcl
      · exact Or.inr (Or.inr ⟨by omega, hx0, h⟩)
  -- the two sign branches share the magnitude comparisons
  rcases hclass x1 hx1w hxhi1 hcase1 with hc1 | hp1 | ⟨hzm1, hx10, hlv1⟩ <;>
    rcases hclass x2 hx2w hxhi2 hcase2 with hc2 | hp2 | ⟨hzm2, hx20, hlv2⟩
  -- (clamp, clamp)
  · rw [mulExpTree_clamped hx1w hc1, mulExpTree_clamped hx2w hc2]
    split <;> exact le_refl _
  -- (clamp, pin)
  · subst hp2
    rw [mulExpTree_clamped hx1w hc1, mulExpTree_scale_point hy habs, int256_zero_word']
    split_ifs with hneg
    · exact le_of_lt hneg
    · exact not_lt.mp hneg
  -- (clamp, live)
  · rw [mulExpTree_clamped hx1w hc1, int256_zero_word']
    have hW2 : WideRegion x2 := ⟨hzm2, hxhi2⟩
    obtain ⟨hm0, _, _, _⟩ := mulMagnitude_bracket_live hy hx2w hy0 habs hx20 hW2 hlv2
    have hm255 := mag_word_small hy hy0 hx2w habs hx20 hW2 hlv2
    by_cases hneg : y < 2 ^ 255
    · rw [if_neg (int256_y_nonneg hneg), int256_tree_pos hypos hneg]
      exact hm0
    · rw [if_pos (int256_y_neg (by omega) hy), int256_tree_neg (by omega) hy hm255]
      linarith [hm0]
  -- (pin, clamp): impossible, the scale point is above the clamp
  · exfalso
    subst hp1
    rw [int256_zero_word'] at hle
    rw [int256_mulExpRayZeroMax] at hc2
    omega
  -- (pin, pin)
  · subst hp1
    subst hp2
    split <;> exact le_refl _
  -- (pin, live): the exponent is positive, the magnitude clears `abs(y)`
  · subst hp1
    have hW2 : WideRegion x2 := ⟨hzm2, hxhi2⟩
    have hx2pos : 0 < int256 x2 := by
      rw [int256_zero_word'] at hle
      omega
    have hge := mulMagnitude_ge_abs_of_pos hy hy0 hx2w habs hW2 hx2pos hlv2
    have hm255 := mag_word_small hy hy0 hx2w habs hx20 hW2 hlv2
    rw [mulExpTree_scale_point hy habs]
    by_cases hneg : y < 2 ^ 255
    · rw [if_neg (int256_y_nonneg hneg), int256_tree_pos hypos hneg, int256_pos_eq_abs hneg]
      exact hge
    · rw [if_pos (int256_y_neg (by omega) hy), int256_tree_neg (by omega) hy hm255,
        int256_neg_eq_abs (by omega) hy]
      linarith [hge]
  -- (live, clamp): impossible
  · exfalso
    rw [int256_mulExpRayZeroMax] at hzm1 hc2
    omega
  -- (live, pin): the exponent is negative, the magnitude stays under `abs(y)`
  · subst hp2
    have hW1 : WideRegion x1 := ⟨hzm1, hxhi1⟩
    have hx1neg : int256 x1 < 0 := by
      rw [int256_zero_word'] at hle
      omega
    have hlt := mulMagnitude_le_abs_of_neg hy hy0 hx1w habs hW1 hx1neg hlv1
    have hm255 := mag_word_small hy hy0 hx1w habs hx10 hW1 hlv1
    rw [mulExpTree_scale_point hy habs]
    by_cases hneg : y < 2 ^ 255
    · rw [if_neg (int256_y_nonneg hneg), int256_tree_pos hypos hneg, int256_pos_eq_abs hneg]
      exact hlt
    · rw [if_pos (int256_y_neg (by omega) hy), int256_tree_neg (by omega) hy hm255,
        int256_neg_eq_abs (by omega) hy]
      linarith [hlt]
  -- (live, live)
  · have hW1 : WideRegion x1 := ⟨hzm1, hxhi1⟩
    have hW2 : WideRegion x2 := ⟨hzm2, hxhi2⟩
    have hmono := mulMagnitude_mono_pair hy hy0 hx1w hx2w habs hW1 hW2 hx10 hx20 hlv1 hlv2 hle
    have hm255a := mag_word_small hy hy0 hx1w habs hx10 hW1 hlv1
    have hm255b := mag_word_small hy hy0 hx2w habs hx20 hW2 hlv2
    by_cases hneg : y < 2 ^ 255
    · rw [if_neg (int256_y_nonneg hneg), int256_tree_pos hypos hneg,
        int256_tree_pos hypos hneg]
      exact hmono
    · rw [if_pos (int256_y_neg (by omega) hy), int256_tree_neg (by omega) hy hm255a,
        int256_tree_neg (by omega) hy hm255b]
      linarith [hmono]

end ExpYul
