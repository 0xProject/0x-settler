import ExpProof.Mul.Domain
import ExpProof.Mul.Shell
import ExpProof.Mono.Quot
import ExpProof.Floor.Spec

/-!
# Shared word transports for the dynamic scale

The `mulExpRay` kernel call runs at the dynamic scale `mulScaleTree y = abs(y)·2^S` and closing
shift `S − k`. This module transports those words to arithmetic facts the accumulator and the
monotonicity arguments consume:

* the headroom shift `S` is at most `127`, and for a nonzero magnitude the scale is *maximal* —
  one more doubling overshoots `scaleQ67` — which pins it into `(scaleQ67/2, scaleQ67]`, so every
  live scale satisfies `2^125 ≤ scale ≤ scaleQ67`;
* the closing-shift word is the signed difference `S − k` on the wide region, and on the live
  region (`2 ≤ shift` from the guard) it is a plain small `Nat` in `[2, 254]`;
* the closing `shr` keeps nonnegative small values small for any shift below the word size.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word

set_option maxRecDepth 100000

/-! ## Word plumbing -/

private theorem u256_self {a : Nat} (h : a < 2 ^ 256) : u256 a = a := u256_of_lt_pow256 h

private theorem evmSub_small {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 256) :
    evmSub a b = a - b := by
  unfold evmSub
  rw [u256_self ha, u256_self (lt_of_le_of_lt hb ha)]
  unfold u256 WORD_MOD
  omega

private theorem evmShl_small {s v : Nat} (hs : s < 256) (hv : v < 2 ^ 256)
    (h : v * 2 ^ s < 2 ^ 256) : evmShl s v = v * 2 ^ s := by
  unfold evmShl
  rw [u256_self (lt_trans hs (by norm_num)), u256_self hv, if_pos hs]
  unfold u256 WORD_MOD
  omega

/-! ## The headroom shift: range and scale maximality -/

/-- The corrected headroom shift, by cases on the magnitude: `127` exactly at zero, and otherwise
at most `126` with the shifted scale maximal (one more doubling overshoots `scaleQ67`). -/
private theorem scaleShiftTree_cases (ay : Nat) (hy : ay < 2 ^ 256) (habs : ay ≤ scaleQ67) :
    (ay = 0 → scaleShiftTree ay = 127) ∧
      (1 ≤ ay → scaleShiftTree ay ≤ 126 ∧
        scaleQ67 < ay * 2 ^ (scaleShiftTree ay + 1)) := by
  constructor
  · intro h0
    subst h0
    have hclz : evmClz 0 = 256 := by
      unfold evmClz
      rw [u256_self (by norm_num)]
      simp
    have hs0 : evmSub 256 scaleMaxClz = 127 := by
      rw [evmSub_small (by unfold scaleMaxClz; omega) (by norm_num)]
      unfold scaleMaxClz
      norm_num
    have hshl : evmShl 127 (0 : Nat) = 0 := by
      rw [evmShl_small (by norm_num) (by norm_num) (by norm_num)]
      ring
    have hgt : evmGt (0 : Nat) scaleQ67 = 0 := by
      unfold evmGt
      rw [u256_self (by norm_num), u256_self (by unfold scaleQ67; norm_num), if_neg (by omega)]
    have hsub : evmSub 127 (0 : Nat) = 127 := evmSub_small (by omega) (by norm_num)
    unfold scaleShiftTree
    simp only [hclz, hs0, hshl, hgt, hsub]
  · intro hpos
    have hlog : Nat.log2 ay ≤ 126 := by
      have h1 : 2 ^ Nat.log2 ay ≤ ay := Nat.log2_self_le (by omega)
      have hQ : scaleQ67 < 2 ^ 127 := by unfold scaleQ67; norm_num
      by_contra h
      push_neg at h
      have h2 : (2 : Nat) ^ 127 ≤ 2 ^ Nat.log2 ay :=
        Nat.pow_le_pow_right (by norm_num) h
      omega
    have hloglo : 2 ^ Nat.log2 ay ≤ ay := Nat.log2_self_le (by omega)
    have hlt : ay < 2 ^ (Nat.log2 ay + 1) := Nat.lt_log2_self
    have hclz : evmClz ay = 255 - Nat.log2 ay := by
      unfold evmClz
      rw [u256_self hy, if_neg (by omega)]
    have hs0eq : evmSub (evmClz ay) scaleMaxClz = 126 - Nat.log2 ay := by
      rw [hclz, evmSub_small (by unfold scaleMaxClz; omega) (by omega)]
      unfold scaleMaxClz
      omega
    have hfit : ay * 2 ^ (126 - Nat.log2 ay) < 2 ^ 127 := by
      calc ay * 2 ^ (126 - Nat.log2 ay)
          < 2 ^ (Nat.log2 ay + 1) * 2 ^ (126 - Nat.log2 ay) :=
            mul_lt_mul_of_pos_right hlt (Nat.two_pow_pos _)
        _ = 2 ^ (Nat.log2 ay + 1 + (126 - Nat.log2 ay)) := by rw [← pow_add]
        _ ≤ 2 ^ 127 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hshl : evmShl (126 - Nat.log2 ay) ay = ay * 2 ^ (126 - Nat.log2 ay) :=
      evmShl_small (by omega) hy (lt_trans hfit (by norm_num))
    -- the uncorrected scale already clears half of scaleQ67: ay·2^(126−log2) ≥ 2^126 > scaleQ67/2
    have hbig : (2 : Nat) ^ 126 ≤ ay * 2 ^ (126 - Nat.log2 ay) := by
      calc (2:Nat) ^ 126 ≤ 2 ^ Nat.log2 ay * 2 ^ (126 - Nat.log2 ay) := by
            rw [← pow_add]
            exact Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ ay * 2 ^ (126 - Nat.log2 ay) := Nat.mul_le_mul_right _ hloglo
    by_cases hover : ay * 2 ^ (126 - Nat.log2 ay) > scaleQ67
    · have hgt : evmGt (ay * 2 ^ (126 - Nat.log2 ay)) scaleQ67 = 1 := by
        unfold evmGt
        rw [u256_self (lt_trans hfit (by norm_num)),
          u256_self (by unfold scaleQ67; norm_num), if_pos hover]
      have hs0pos : 0 < 126 - Nat.log2 ay := by
        rcases Nat.eq_zero_or_pos (126 - Nat.log2 ay) with h | h
        · rw [h] at hover
          simp at hover
          omega
        · exact h
      have hsub : evmSub (126 - Nat.log2 ay) 1 = 126 - Nat.log2 ay - 1 :=
        evmSub_small (by omega) (by omega)
      have hsst : scaleShiftTree ay = 126 - Nat.log2 ay - 1 := by
        unfold scaleShiftTree
        simp only [hs0eq, hshl, hgt, hsub]
      refine ⟨by omega, ?_⟩
      rw [hsst]
      have hexp : 126 - Nat.log2 ay - 1 + 1 = 126 - Nat.log2 ay := by omega
      rw [hexp]
      exact hover
    · have hgt : evmGt (ay * 2 ^ (126 - Nat.log2 ay)) scaleQ67 = 0 := by
        unfold evmGt
        rw [u256_self (lt_trans hfit (by norm_num)),
          u256_self (by unfold scaleQ67; norm_num), if_neg hover]
      have hsub : evmSub (126 - Nat.log2 ay) 0 = 126 - Nat.log2 ay :=
        evmSub_small (by omega) (by omega)
      have hsst : scaleShiftTree ay = 126 - Nat.log2 ay := by
        unfold scaleShiftTree
        simp only [hs0eq, hshl, hgt, hsub]
      refine ⟨by omega, ?_⟩
      rw [hsst]
      -- doubling the uncorrected scale clears 2^127 > scaleQ67
      have hQ : scaleQ67 < 2 ^ 127 := by unfold scaleQ67; norm_num
      calc scaleQ67 < 2 ^ 127 := hQ
        _ = 2 ^ 126 * 2 := by ring
        _ ≤ ay * 2 ^ (126 - Nat.log2 ay) * 2 := Nat.mul_le_mul_right _ hbig
        _ = ay * 2 ^ (126 - Nat.log2 ay + 1) := by rw [pow_succ]; ring

/-- The zero magnitude takes the maximal headroom shift. -/
theorem scaleShiftTree_zero : scaleShiftTree 0 = 127 :=
  (scaleShiftTree_cases 0 (by norm_num) (by unfold scaleQ67; norm_num)).1 rfl

/-- The headroom shift never exceeds `127` on supported magnitudes. -/
theorem scaleShiftTree_le_127 {y : Nat} (habs : absTree y ≤ scaleQ67) :
    scaleShiftTree (absTree y) ≤ 127 := by
  obtain ⟨h0, hpos⟩ := scaleShiftTree_cases (absTree y) (absTree_lt y) habs
  rcases Nat.eq_zero_or_pos (absTree y) with h | h
  · omega
  · have := (hpos h).1
    omega

/-- **Scale maximality.** For a nonzero supported magnitude, one more doubling of the headroom
scale overshoots `scaleQ67`. -/
theorem mulScaleTree_max {y : Nat} (hy : y < 2 ^ 256) (hpos : 1 ≤ absTree y)
    (habs : absTree y ≤ scaleQ67) : scaleQ67 < 2 * mulScaleTree y := by
  obtain ⟨_, hspec, _⟩ := mulScaleTree_spec hy habs
  obtain ⟨_, hposcase⟩ := scaleShiftTree_cases (absTree y) (absTree_lt y) habs
  obtain ⟨_, hmax⟩ := hposcase hpos
  rw [hspec]
  calc scaleQ67 < absTree y * 2 ^ (scaleShiftTree (absTree y) + 1) := hmax
    _ = 2 * (absTree y * 2 ^ scaleShiftTree (absTree y)) := by rw [pow_succ]; ring

/-- **Scale lower bound.** Every nonzero supported magnitude's headroom scale is at least
`2^125`. -/
theorem mulScaleTree_lower {y : Nat} (hy : y < 2 ^ 256) (hpos : 1 ≤ absTree y)
    (habs : absTree y ≤ scaleQ67) : 2 ^ 125 ≤ mulScaleTree y := by
  have hmax := mulScaleTree_max hy hpos habs
  have hQ : (2:Nat) ^ 126 ≤ scaleQ67 := by unfold scaleQ67; norm_num
  omega

/-! ## The closing-shift word -/

/-- The closing-shift word carries the signed difference `S − k` on the wide region. -/
theorem mulShiftTree_transport {y x : Nat} (hy : y < 2 ^ 256) (hx : x < 2 ^ 256)
    (habs : absTree y ≤ scaleQ67) (hW : WideRegion x) :
    int256 (mulShiftTree y x) =
      (scaleShiftTree (absTree y) : Int) - int256 (kTree x) := by
  have hs127 := scaleShiftTree_le_127 habs
  obtain ⟨hklo, hkhi⟩ := kTree_bound_wide hx hW
  have hsw : scaleShiftTree (absTree y) < 2 ^ 256 := scaleShiftTree_lt _
  have hkw : kTree x < 2 ^ 256 := by unfold kTree; exact evmSar_lt _ _
  have hsi : int256 (scaleShiftTree (absTree y)) = (scaleShiftTree (absTree y) : Int) :=
    int256_of_lt (by
      have : (127:Nat) < 2 ^ 255 := by norm_num
      omega)
  unfold mulShiftTree
  rw [evmSub_transport hsw hkw ?_ ?_, hsi]
  · rw [hsi]
    have hs : (scaleShiftTree (absTree y) : Int) ≤ 127 := by exact_mod_cast hs127
    have hs0 : (0 : Int) ≤ (scaleShiftTree (absTree y) : Int) := Int.natCast_nonneg _
    simp only [ipow255]
    linarith [hs, hs0, hklo, hkhi]
  · rw [hsi]
    have hs0 : (0 : Int) ≤ (scaleShiftTree (absTree y) : Int) := Int.natCast_nonneg _
    have hs : (scaleShiftTree (absTree y) : Int) ≤ 127 := by exact_mod_cast hs127
    simp only [ipow255]
    linarith [hs, hs0, hklo, hkhi]

/-- On the live region the closing-shift word is a plain small `Nat` in `[2, 254]`, equal to
`S − k` on the signed side. -/
theorem mulShift_word_facts {y x : Nat} (hy : y < 2 ^ 256) (hx : x < 2 ^ 256)
    (habs : absTree y ≤ scaleQ67) (hW : WideRegion x)
    (hlive : 2 ≤ int256 (mulShiftTree y x)) :
    2 ≤ mulShiftTree y x ∧ mulShiftTree y x < 256 ∧
      (mulShiftTree y x : Int) = int256 (mulShiftTree y x) := by
  have htrans := mulShiftTree_transport hy hx habs hW
  have hs127 := scaleShiftTree_le_127 habs
  obtain ⟨hklo, hkhi⟩ := kTree_bound_wide hx hW
  have hs : (scaleShiftTree (absTree y) : Int) ≤ 127 := by exact_mod_cast hs127
  have hhi : int256 (mulShiftTree y x) ≤ 254 := by
    rw [htrans]
    omega
  have hword : mulShiftTree y x < 2 ^ 256 := mulShiftTree_lt y x
  have hnn : 0 ≤ int256 (mulShiftTree y x) := by omega
  obtain ⟨heq, _⟩ := int256_eq_of_nonneg hword hnn
  refine ⟨?_, ?_, heq.symm⟩
  · have : (2 : Int) ≤ (mulShiftTree y x : Int) := by rw [← heq]; exact hlive
    exact_mod_cast this
  · have : (mulShiftTree y x : Int) ≤ 254 := by rw [← heq]; exact hhi
    have h254 : mulShiftTree y x ≤ 254 := by exact_mod_cast this
    omega

/-- Closing `shr` at any shift `s ∈ [2, 255]`: a nonnegative argument below `2^130` floors to a
nonnegative value below `2^128`. -/
theorem mulShr_facts {W s : Nat} (hWw : W < 2 ^ 256) (hslo : 2 ≤ s) (hshi : s ≤ 255)
    (hWnn : 0 ≤ int256 W) (hWhi : int256 W < 2 ^ 130) :
    0 ≤ int256 (evmShr s W) ∧ int256 (evmShr s W) < 2 ^ 128 := by
  obtain ⟨hWi, _⟩ := int256_eq_of_nonneg hWw hWnn
  have hWnat : W < 2 ^ 130 := by
    have : ((W : Nat) : Int) < 2 ^ 130 := by rw [← hWi]; exact hWhi
    exact_mod_cast this
  rw [evmShr_eq_div (by omega) hWw]
  have hqlt : W / 2 ^ s < 2 ^ 128 := by
    have h4 : (2:Nat) ^ 2 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hslo
    have h1 : W / 2 ^ s ≤ W / 2 ^ 2 := Nat.div_le_div_left h4 (Nat.two_pow_pos _)
    have h2 : W / 2 ^ 2 < 2 ^ 128 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      calc W < 2 ^ 130 := hWnat
        _ = 2 ^ 128 * 2 ^ 2 := by rw [← Nat.pow_add]
    omega
  rw [int256_of_lt (by
    have : (2:Nat) ^ 128 < 2 ^ 255 := by norm_num
    omega)]
  constructor
  · positivity
  · exact_mod_cast hqlt

end ExpYul
