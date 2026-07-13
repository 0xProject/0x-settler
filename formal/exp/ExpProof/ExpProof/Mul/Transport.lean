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
  every supported magnitude is normalized at or immediately below bit 126, except the inclusive
  `2^127` endpoint, which stays at that endpoint, so every live scale satisfies
  `2^125 ≤ scale ≤ kernelScaleMax`;
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

/-- Every positive supported magnitude aligns its highest set bit with bit 126, except the
inclusive endpoint, whose normalization shift is zero. -/
theorem scaleShiftTree_pos {ay : Nat} (hy : ay < 2 ^ 256)
    (hpos : 1 ≤ ay) (habs : ay ≤ kernelScaleMax) :
    scaleShiftTree ay = 126 - Nat.log2 ay := by
  by_cases hend : ay = kernelScaleMax
  · rw [hend, kernelScaleMax_eq]
    have hloglo : 127 ≤ Nat.log2 (2 ^ 127) :=
      (Nat.le_log2 (by norm_num)).2 (by norm_num)
    have hloghi : Nat.log2 (2 ^ 127) < 128 :=
      (Nat.log2_lt (by norm_num)).2 (by norm_num)
    have hlog : Nat.log2 (2 ^ 127) = 127 := by omega
    have hclz : evmClz (2 ^ 127) = 128 := by
      unfold evmClz
      rw [u256_self (by norm_num), if_neg (by norm_num), hlog]
    have hsub : evmSub 128 scaleClzBias = 2 ^ 256 - 1 := by
      norm_num [evmSub, scaleClzBias, u256, WORD_MOD]
    have hshr : evmShr 127 (2 ^ 127) = 1 := by
      norm_num [evmShr, u256, WORD_MOD]
    unfold scaleShiftTree
    rw [hclz, hsub, hshr]
    have hadd : evmAdd (2 ^ 256 - 1) 1 = 0 := by
      norm_num [evmAdd, u256, WORD_MOD]
    rw [hadd]
    change 0 = 126 - Nat.log2 (2 ^ 127)
    rw [hlog]
  · have hay127 : ay < 2 ^ 127 := by rw [← kernelScaleMax_eq]; omega
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
    have hshr : evmShr 127 ay = 0 := by
      unfold evmShr
      rw [u256_self (by norm_num), u256_self hy, if_pos (by norm_num)]
      exact Nat.div_eq_of_lt hay127
    have hsub : evmSub (255 - Nat.log2 ay) scaleClzBias = 126 - Nat.log2 ay := by
      rw [evmSub_small (by unfold scaleClzBias; omega) (by omega)]
      unfold scaleClzBias
      omega
    unfold scaleShiftTree
    rw [hclz, hshr, hsub]
    unfold evmAdd
    have hshiftlt : 126 - Nat.log2 ay < 2 ^ 256 :=
      lt_of_le_of_lt (Nat.sub_le _ _) (by norm_num)
    rw [show u256 (126 - Nat.log2 ay) = 126 - Nat.log2 ay from u256_self hshiftlt,
      show u256 0 = 0 from u256_self (by norm_num)]
    rw [Nat.add_zero, u256_self hshiftlt]

theorem scaleShiftTree_zero : scaleShiftTree 0 = 127 := by
  have hclz : evmClz 0 = 256 := by
    unfold evmClz
    rw [u256_self (by norm_num)]
    simp
  unfold scaleShiftTree
  rw [hclz, evmSub_small (by unfold scaleClzBias; omega) (by norm_num)]
  norm_num [scaleClzBias, evmShr, evmAdd, u256, WORD_MOD]

theorem scaleShiftTree_int128Max : scaleShiftTree int128Max = 0 := by
  have hmax : int128Max ≠ 0 := by unfold int128Max; norm_num
  have hloglo : 126 ≤ Nat.log2 int128Max :=
    (Nat.le_log2 hmax).2 (by unfold int128Max; norm_num)
  have hloghi : Nat.log2 int128Max < 127 :=
    (Nat.log2_lt hmax).2 (by unfold int128Max; norm_num)
  have hlog : Nat.log2 int128Max = 126 := by omega
  rw [scaleShiftTree_pos (by unfold int128Max; norm_num) (by unfold int128Max; norm_num)
    (by rw [int128Max_eq, kernelScaleMax_eq]; omega), hlog]

theorem scaleShiftTree_kernelScaleMax : scaleShiftTree kernelScaleMax = 0 := by
  rw [scaleShiftTree_pos (by unfold kernelScaleMax; norm_num)
    (by unfold kernelScaleMax; norm_num) (le_refl _), kernelScaleMax_eq]
  have hloglo : 127 ≤ Nat.log2 (2 ^ 127) :=
    (Nat.le_log2 (by norm_num)).2 (by norm_num)
  have hloghi : Nat.log2 (2 ^ 127) < 128 :=
    (Nat.log2_lt (by norm_num)).2 (by norm_num)
  omega

theorem scaleShiftTree_le_127 {y : Nat} (habs : absTree y ≤ kernelScaleMax) :
    scaleShiftTree (absTree y) ≤ 127 := by
  rcases Nat.eq_zero_or_pos (absTree y) with h0 | hpos
  · rw [h0, scaleShiftTree_zero]
  · rw [scaleShiftTree_pos (absTree_lt y) hpos habs]
    omega

/-- One more doubling of every nonzero normalized scale reaches the inclusive analytic cap. -/
theorem mulScaleTree_max {y : Nat} (hy : y < 2 ^ 256) (hpos : 1 ≤ absTree y)
    (habs : absTree y ≤ kernelScaleMax) : kernelScaleMax ≤ 2 * mulScaleTree y := by
  obtain ⟨_, hscale, _⟩ := mulScaleTree_spec hy habs
  by_cases hend : absTree y = kernelScaleMax
  · rw [hscale, hend, scaleShiftTree_kernelScaleMax, kernelScaleMax_eq]
    norm_num
  have hs := scaleShiftTree_pos (absTree_lt y) hpos habs
  have hloglo : 2 ^ Nat.log2 (absTree y) ≤ absTree y :=
    Nat.log2_self_le (by omega)
  have hlog : Nat.log2 (absTree y) ≤ 126 := by
    have hay127 : absTree y < 2 ^ 127 := by rw [← kernelScaleMax_eq]; omega
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
  rw [hscale, hs, kernelScaleMax_eq]
  omega

/-- Every nonzero supported magnitude's normalized scale is at least 2^125. -/
theorem mulScaleTree_lower {y : Nat} (hy : y < 2 ^ 256) (hpos : 1 ≤ absTree y)
    (habs : absTree y ≤ kernelScaleMax) : 2 ^ 125 ≤ mulScaleTree y := by
  have hmax := mulScaleTree_max hy hpos habs
  have hQ : (2 : Nat) ^ 126 ≤ kernelScaleMax := by
    unfold kernelScaleMax
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
theorem mulShiftTree_transport_global {y x : Nat} (habs : absTree y ≤ kernelScaleMax) :
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
theorem int128Max_octave_neg_two_valueDomain {x : Nat} (hx : x < 2 ^ 256)
    (hxhi : int256 x < int256 mulExpRayHi) (hk : int256 (kTree x) = -2) :
    scaleShiftTree (absTree int128Max) = 0 ∧
      int256 (mulShiftTree int128Max x) = 2 ∧
        MulExpRayValueDomain int128Max x := by
  have hy : int128Max < 2 ^ 256 := by unfold int128Max; norm_num
  have habs : absTree int128Max = int128Max :=
    absTree_nonneg (by unfold int128Max; norm_num)
  have hcap : absTree int128Max ≤ kernelScaleMax := by
    rw [habs, int128Max_eq, kernelScaleMax_eq]
    omega
  have hs : scaleShiftTree (absTree int128Max) = 0 := by rw [habs, scaleShiftTree_int128Max]
  have hshift : int256 (mulShiftTree int128Max x) = 2 := by
    rw [mulShiftTree_transport_global hcap, hs, hk]
    norm_num
  exact ⟨hs, hshift,
    ⟨⟨int128Word_max, hx⟩, hxhi, by omega⟩⟩

theorem int128Min_octave_neg_two_valueDomain {x : Nat} (hx : x < 2 ^ 256)
    (hxhi : int256 x < int256 mulExpRayHi) (hk : int256 (kTree x) = -2) :
    scaleShiftTree (absTree (2 ^ 256 - 2 ^ 127)) = 0 ∧
      int256 (mulShiftTree (2 ^ 256 - 2 ^ 127) x) = 2 ∧
        MulExpRayValueDomain (2 ^ 256 - 2 ^ 127) x := by
  have hy : 2 ^ 256 - 2 ^ 127 < 2 ^ 256 := by norm_num
  have habs : absTree (2 ^ 256 - 2 ^ 127) = kernelScaleMax := by
    rw [absTree_neg (by norm_num) hy, kernelScaleMax_eq]
    omega
  have hcap : absTree (2 ^ 256 - 2 ^ 127) ≤ kernelScaleMax := by rw [habs]
  have hs : scaleShiftTree (absTree (2 ^ 256 - 2 ^ 127)) = 0 := by
    rw [habs, scaleShiftTree_kernelScaleMax]
  have hshift : int256 (mulShiftTree (2 ^ 256 - 2 ^ 127) x) = 2 := by
    rw [mulShiftTree_transport_global hcap, hs, hk]
    norm_num
  exact ⟨hs, hshift, ⟨⟨int128Word_min, hx⟩, hxhi, by omega⟩⟩

theorem int128Min_valueDomain_iff {x : Nat} (hx : x < 2 ^ 256) :
    MulExpRayValueDomain (2 ^ 256 - 2 ^ 127) x ↔
      int256 x < int256 mulExpRayHi ∧ int256 (kTree x) ≤ -2 := by
  have hy : 2 ^ 256 - 2 ^ 127 < 2 ^ 256 := by norm_num
  have habs : absTree (2 ^ 256 - 2 ^ 127) = kernelScaleMax := by
    rw [absTree_neg (by norm_num) hy, kernelScaleMax_eq]
    omega
  have hcap : absTree (2 ^ 256 - 2 ^ 127) ≤ kernelScaleMax := by rw [habs]
  have hshift : int256 (mulShiftTree (2 ^ 256 - 2 ^ 127) x) = -int256 (kTree x) := by
    rw [mulShiftTree_transport_global hcap, habs, scaleShiftTree_kernelScaleMax]
    ring
  constructor
  · rintro ⟨_, hxhi, hlive⟩
    rw [hshift] at hlive
    omega
  · rintro ⟨hxhi, hk⟩
    refine ⟨⟨int128Word_min, hx⟩, hxhi, ?_⟩
    rw [hshift]
    omega

/-- The closing-shift word carries the signed difference `S − k` on the wide region. -/
theorem mulShiftTree_transport {y x : Nat} (_hy : y < 2 ^ 256) (_hx : x < 2 ^ 256)
    (habs : absTree y ≤ kernelScaleMax) (_hW : WideRegion x) :
    int256 (mulShiftTree y x) =
      (scaleShiftTree (absTree y) : Int) - int256 (kTree x) :=
  mulShiftTree_transport_global habs

/-- On the live region the closing-shift word is a plain small `Nat` in `[2, 254]`, equal to
`S − k` on the signed side. -/
theorem mulShift_word_facts {y x : Nat} (hy : y < 2 ^ 256) (hx : x < 2 ^ 256)
    (habs : absTree y ≤ kernelScaleMax) (hW : WideRegion x)
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

/-- Closing `shr` at any shift `s ∈ [2, 255]`: a nonnegative argument below `2^129` floors to a
nonnegative value below `2^127`. -/
theorem mulShr_facts {W s : Nat} (hWw : W < 2 ^ 256) (hslo : 2 ≤ s) (hshi : s ≤ 255)
    (hWnn : 0 ≤ int256 W) (hWhi : int256 W < 2 ^ 129) :
    0 ≤ int256 (evmShr s W) ∧ int256 (evmShr s W) < 2 ^ 127 := by
  obtain ⟨hWi, _⟩ := int256_eq_of_nonneg hWw hWnn
  have hWnat : W < 2 ^ 129 := by
    have : ((W : Nat) : Int) < 2 ^ 129 := by rw [← hWi]; exact hWhi
    exact_mod_cast this
  rw [evmShr_eq_div (by omega) hWw]
  have hqlt : W / 2 ^ s < 2 ^ 127 := by
    have h4 : (2:Nat) ^ 2 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hslo
    have h1 : W / 2 ^ s ≤ W / 2 ^ 2 := Nat.div_le_div_left h4 (Nat.two_pow_pos _)
    have h2 : W / 2 ^ 2 < 2 ^ 127 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      calc W < 2 ^ 129 := hWnat
        _ = 2 ^ 127 * 2 ^ 2 := by rw [← Nat.pow_add]
    omega
  rw [int256_of_lt (by
    have : (2:Nat) ^ 127 < 2 ^ 255 := by norm_num
    omega)]
  constructor
  · positivity
  · exact_mod_cast hqlt

end ExpYul
