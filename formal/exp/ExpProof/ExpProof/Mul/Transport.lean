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
  the all-ones 127-bit cap aligns every nonzero supported magnitude into `[2^126, 2^127)`, so every
  live scale satisfies `2^125 ≤ scale ≤ scaleMax`;
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

/-! ## The headroom shift and normalized scale -/

/-- Every positive supported magnitude aligns its highest set bit with bit 126. -/
private theorem scaleShiftTree_pos {ay : Nat} (hy : ay < 2 ^ 256)
    (hpos : 1 ≤ ay) (habs : ay ≤ scaleMax) :
    scaleShiftTree ay = 126 - Nat.log2 ay := by
  have hay127 : ay < 2 ^ 127 := lt_of_le_of_lt habs scaleMax_lt_2127
  have hlog : Nat.log2 ay ≤ 126 := by
    have h1 : 2 ^ Nat.log2 ay ≤ ay := Nat.log2_self_le (by omega)
    by_contra h
    push_neg at h
    have h2 : (2 : Nat) ^ 127 ≤ 2 ^ Nat.log2 ay :=
      Nat.pow_le_pow_right (by norm_num) h
    omega
  have hclz : evmClz ay = 255 - Nat.log2 ay := by
    unfold evmClz
    rw [u256_self hy, if_neg (by omega)]
  unfold scaleShiftTree
  rw [hclz, evmSub_small (by unfold scaleMaxClz; omega) (by omega)]
  unfold scaleMaxClz
  omega

/-- The zero magnitude takes the maximal headroom shift. -/
theorem scaleShiftTree_zero : scaleShiftTree 0 = 127 := by
  have hclz : evmClz 0 = 256 := by
    unfold evmClz
    rw [u256_self (by norm_num)]
    simp
  unfold scaleShiftTree
  rw [hclz, evmSub_small (by unfold scaleMaxClz; omega) (by norm_num)]
  unfold scaleMaxClz
  norm_num

/-- The maximal supported magnitude has no normalization headroom. -/
theorem scaleShiftTree_scaleMax : scaleShiftTree scaleMax = 0 := by
  have hscaleMax : scaleMax ≠ 0 := by unfold scaleMax; norm_num
  have hloglo : 126 ≤ Nat.log2 scaleMax :=
    (Nat.le_log2 hscaleMax).2 (by unfold scaleMax; norm_num)
  have hloghi : Nat.log2 scaleMax < 127 :=
    (Nat.log2_lt hscaleMax).2 (by unfold scaleMax; norm_num)
  have hlog : Nat.log2 scaleMax = 126 := by omega
  rw [scaleShiftTree_pos (by unfold scaleMax; norm_num) (by unfold scaleMax; norm_num)
    (le_refl _), hlog]

/-- The headroom shift never exceeds 127 on supported magnitudes. -/
theorem scaleShiftTree_le_127 {y : Nat} (habs : absTree y ≤ scaleMax) :
    scaleShiftTree (absTree y) ≤ 127 := by
  rcases Nat.eq_zero_or_pos (absTree y) with h0 | hpos
  · rw [h0, scaleShiftTree_zero]
  · rw [scaleShiftTree_pos (absTree_lt y) hpos habs]
    omega

/-- The derived headroom guard is exactly the 127-bit magnitude cap. -/
theorem scaleShiftTree_le_127_iff {ay : Nat} (hay : ay < 2 ^ 256) :
    scaleShiftTree ay ≤ 127 ↔ ay ≤ scaleMax := by
  constructor
  · intro hs
    by_contra hcap
    push_neg at hcap
    have haylo : 2 ^ 127 ≤ ay := by
      rw [scaleMax_eq] at hcap
      omega
    have hpos : 1 ≤ ay := by omega
    have hloglo : 127 ≤ Nat.log2 ay := by
      by_contra h
      push_neg at h
      have hlt := Nat.lt_log2_self (n := ay)
      have hp : (2 : Nat) ^ (Nat.log2 ay + 1) ≤ 2 ^ 127 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hloghi : Nat.log2 ay ≤ 255 := by
      have hp := Nat.log2_self_le (by omega : ay ≠ 0)
      by_contra h
      push_neg at h
      have hpow : (2 : Nat) ^ 256 ≤ 2 ^ Nat.log2 ay :=
        Nat.pow_le_pow_right (by norm_num) h
      omega
    have hclz : evmClz ay = 255 - Nat.log2 ay := by
      unfold evmClz
      rw [u256_self hay, if_neg (by omega)]
    have hc : 255 - Nat.log2 ay < 129 := by omega
    have hraw : 255 - Nat.log2 ay + 2 ^ 256 - 129 < 2 ^ 256 := by
      omega
    have hsub : scaleShiftTree ay = 255 - Nat.log2 ay + 2 ^ 256 - 129 := by
      unfold scaleShiftTree
      rw [hclz, evmSub_eq_mod_pow256 (by omega) (by unfold scaleMaxClz; norm_num)]
      unfold scaleMaxClz
      rw [Nat.mod_eq_of_lt hraw]
    rw [hsub] at hs
    omega
  · intro hcap
    rcases Nat.eq_zero_or_pos ay with h0 | hpos
    · rw [h0, scaleShiftTree_zero]
    · rw [scaleShiftTree_pos hay hpos hcap]
      omega

/-- Scale maximality: for a nonzero supported magnitude, one more doubling of the normalized
scale exceeds the 127-bit cap. -/
theorem mulScaleTree_max {y : Nat} (hy : y < 2 ^ 256) (hpos : 1 ≤ absTree y)
    (habs : absTree y ≤ scaleMax) : scaleMax < 2 * mulScaleTree y := by
  obtain ⟨_, hscale, _⟩ := mulScaleTree_spec hy habs
  have hs := scaleShiftTree_pos (absTree_lt y) hpos habs
  have hloglo : 2 ^ Nat.log2 (absTree y) ≤ absTree y :=
    Nat.log2_self_le (by omega)
  have hlog : Nat.log2 (absTree y) ≤ 126 := by
    have hay127 : absTree y < 2 ^ 127 :=
      lt_of_le_of_lt habs scaleMax_lt_2127
    by_contra h
    push_neg at h
    have h2 : (2 : Nat) ^ 127 ≤ 2 ^ Nat.log2 (absTree y) :=
      Nat.pow_le_pow_right (by norm_num) h
    omega
  have hbig : (2 : Nat) ^ 126 ≤
      absTree y * 2 ^ (126 - Nat.log2 (absTree y)) := by
    calc (2 : Nat) ^ 126
        ≤ 2 ^ Nat.log2 (absTree y) *
            2 ^ (126 - Nat.log2 (absTree y)) := by
          rw [← pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ absTree y * 2 ^ (126 - Nat.log2 (absTree y)) :=
        Nat.mul_le_mul_right _ hloglo
  rw [hscale, hs, scaleMax_eq]
  omega

/-- Every nonzero supported magnitude's normalized scale is at least 2^125. -/
theorem mulScaleTree_lower {y : Nat} (hy : y < 2 ^ 256) (hpos : 1 ≤ absTree y)
    (habs : absTree y ≤ scaleMax) : 2 ^ 125 ≤ mulScaleTree y := by
  have hmax := mulScaleTree_max hy hpos habs
  have hQ : (2 : Nat) ^ 126 ≤ scaleMax := by
    unfold scaleMax
    norm_num
  omega
/-! ## The closing-shift word -/

/-- The arithmetic right shift that forms the octave index keeps it in a signed 64-bit range,
independently of the exponent word. -/
theorem kTree_global_bounds (x : Nat) :
    -(2 ^ 63) ≤ int256 (kTree x) ∧ int256 (kTree x) < 2 ^ 63 := by
  set w := evmAdd (evmShl kHalfShift 1) (evmMul cInvQ192 x) with hwdef
  have hw : w < 2 ^ 256 := by
    rw [hwdef]
    exact evmAdd_lt _ _
  have hword : -(2 ^ 255) ≤ int256 w ∧ int256 w < 2 ^ 255 := by
    unfold int256
    split_ifs <;> omega
  have hsar := Common.Word.evmSar_sandwich (s := kRoundShift)
    (by unfold kRoundShift; norm_num) hw
  have hk : kTree x = evmSar kRoundShift w := by rw [hwdef]; rfl
  rw [← hk] at hsar
  unfold kRoundShift at hsar
  constructor <;> nlinarith [hword.1, hword.2, hsar.2.1, hsar.2.2]

/-- The closing shift carries the signed difference globally on supported magnitudes. The octave
word's signed 64-bit range leaves ample room for the headroom shift in `[0, 127]`, so the EVM
subtraction cannot cross either signed boundary. -/
theorem mulShiftTree_transport_global {y x : Nat} (habs : absTree y ≤ scaleMax) :
    int256 (mulShiftTree y x) =
      (scaleShiftTree (absTree y) : Int) - int256 (kTree x) := by
  have hs127 := scaleShiftTree_le_127 habs
  obtain ⟨hklo, hkhi⟩ := kTree_global_bounds x
  have hsw : scaleShiftTree (absTree y) < 2 ^ 256 := scaleShiftTree_lt _
  have hkw : kTree x < 2 ^ 256 := by unfold kTree; exact evmSar_lt _ _
  have hsi : int256 (scaleShiftTree (absTree y)) = (scaleShiftTree (absTree y) : Int) :=
    int256_of_lt (by omega)
  unfold mulShiftTree
  rw [evmSub_transport hsw hkw ?_ ?_, hsi]
  · rw [hsi]
    have hs0 : (0 : Int) ≤ (scaleShiftTree (absTree y) : Int) := Int.natCast_nonneg _
    have hs : (scaleShiftTree (absTree y) : Int) ≤ 127 := by exact_mod_cast hs127
    simp only [ipow255]
    nlinarith [hs0, hs, hklo, hkhi]
  · rw [hsi]
    have hs0 : (0 : Int) ≤ (scaleShiftTree (absTree y) : Int) := Int.natCast_nonneg _
    have hs : (scaleShiftTree (absTree y) : Int) ≤ 127 := by exact_mod_cast hs127
    simp only [ipow255]
    nlinarith [hs0, hs, hklo, hkhi]

/-- At the magnitude cap, an exponent in octave `-2` has exactly the minimum accepted closing
shift and lies in the value domain whenever it is below the unconditional upper fence. -/
theorem scaleMax_octave_neg_two_valueDomain {x : Nat} (hx : x < 2 ^ 256)
    (hxhi : int256 x < int256 mulExpRayHi) (hk : int256 (kTree x) = -2) :
    scaleShiftTree (absTree scaleMax) = 0 ∧
      int256 (mulShiftTree scaleMax x) = 2 ∧
        MulExpRayValueDomain scaleMax x := by
  have hy : scaleMax < 2 ^ 256 := by unfold scaleMax; norm_num
  have habs : absTree scaleMax = scaleMax :=
    absTree_nonneg (by unfold scaleMax; norm_num)
  have hcap : absTree scaleMax ≤ scaleMax := by rw [habs]
  have hs : scaleShiftTree (absTree scaleMax) = 0 := by rw [habs, scaleShiftTree_scaleMax]
  have hshift : int256 (mulShiftTree scaleMax x) = 2 := by
    rw [mulShiftTree_transport_global hcap, hs, hk]
    norm_num
  exact ⟨hs, hshift,
    ⟨⟨int128CalldataWord_scaleMax, hx⟩, by rw [hs]; norm_num, hxhi, by omega⟩⟩

/-- The closing-shift word carries the signed difference `S − k` on the wide region. -/
theorem mulShiftTree_transport {y x : Nat} (_hy : y < 2 ^ 256) (_hx : x < 2 ^ 256)
    (habs : absTree y ≤ scaleMax) (_hW : WideRegion x) :
    int256 (mulShiftTree y x) =
      (scaleShiftTree (absTree y) : Int) - int256 (kTree x) :=
  mulShiftTree_transport_global habs

/-- On the live region the closing-shift word is a plain small `Nat` in `[2, 254]`, equal to
`S − k` on the signed side. -/
theorem mulShift_word_facts {y x : Nat} (hy : y < 2 ^ 256) (hx : x < 2 ^ 256)
    (habs : absTree y ≤ scaleMax) (hW : WideRegion x)
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
