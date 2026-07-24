import ExpProof.Mul.Transport
import ExpProof.Floor.R0ExpUnder

/-!
# The live-region accumulator of `mulExpRay`

On the live region — `x` strictly between the zero clamp and the overflow guard, a nonzero
magnitude, and at least two bits of closing shift — the kernel magnitude is the closing shift of
the decremented dynamic-scale quotient. The scale-symbolic per-point brackets
(`r0Scaled_real_over_within`/`r0Scaled_real_under_within`) confine that quotient to
`(scale·exp(rt) − 2993/1000 − 1, scale·exp(rt) + 1)` at `scale = mulScaleTree y ∈
[2^125, kernelScaleMax]`, and the target fold `A·2^shift = scale·exp(rt)`
(`A = abs(y)·exp(x/10²⁷)`)
turns the `shr` floor sandwich into the two-unit magnitude bracket `0 ≤ m ≤ A < m + 2`. Sign
reapplication then yields the public signed bracket on the whole value domain, with the floor
membership `m ∈ {⌊A⌋, ⌊A⌋ − 1}` and the `A < 1 → m = 0` pin as corollaries.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word
open ExpRealSpec

set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

/-! ## Word plumbing -/

private theorem u256_self {a : Nat} (h : a < 2 ^ 256) : u256 a = a := u256_of_lt_pow256 h

private theorem evmSub_small {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 256) :
    evmSub a b = a - b := by
  unfold evmSub
  rw [u256_self ha, u256_self (lt_of_le_of_lt hb ha)]
  unfold u256 WORD_MOD
  omega

private theorem evmAdd_zero_left {W : Nat} (hW : W < 2 ^ 256) : evmAdd 0 W = W := by
  unfold evmAdd
  rw [u256_self (a := 0) (by norm_num), u256_self (a := W) hW, Nat.zero_add]
  exact u256_self hW

private theorem evmMul_one_left {W : Nat} (hW : W < 2 ^ 256) : evmMul 1 W = W := by
  unfold evmMul
  rw [u256_self (a := 1) (by norm_num), u256_self (a := W) hW, Nat.one_mul]
  exact u256_self hW

private theorem int256_zero_word : int256 (0 : Nat) = 0 := by unfold int256; norm_num

/-- A nonzero word has a nonzero magnitude. -/
theorem absTree_pos {y : Nat} (hy : y < 2 ^ 256) (hy0 : y ≠ 0) : 1 ≤ absTree y := by
  by_cases hneg : y < 2 ^ 255
  · rw [absTree_nonneg hneg]
    omega
  · rw [absTree_neg (by omega) hy]
    omega

/-- On the live region the magnitude word is the closing shift of the decremented quotient:
the pin and the clamp multiplier are both inert. -/
theorem mulMagnitudeTree_live {y x : Nat} (hx : x < 2 ^ 256)
    (hx0 : int256 x ≠ 0) (hxgt : int256 mulExpRayZeroMax < int256 x) :
    mulMagnitudeTree y x =
      evmShr (mulShiftTree y x) (evmSub (r0MulTree y x) marginWord) := by
  have hxw0 : x ≠ 0 := by
    intro h
    subst h
    exact hx0 int256_zero_word
  have hslt : evmSlt mulExpRayZeroMax x = 1 := by
    rw [evmSlt_eq_ite, u256_self mulExpRayZeroMax_lt, u256_self hx, if_pos hxgt]
  have hisz : evmIszero x = 0 := by
    unfold evmIszero
    rw [u256_self hx, if_neg hxw0]
  unfold mulMagnitudeTree
  rw [hslt, hisz, evmMul_one_left (evmShr_lt _ _), evmAdd_zero_left (evmShr_lt _ _)]

noncomputable section

/-! ## The live-region magnitude bracket -/

/-- **Live-region magnitude bracket.** On the live region the kernel magnitude `m` is a
nonnegative value below `2^127` with `m ≤ A < m + 2`. -/
theorem mulMagnitude_bracket_live {y x : Nat} (hy : y < 2 ^ 256) (hx : x < 2 ^ 256)
    (hy0 : y ≠ 0) (habs : absTree y ≤ kernelScaleMax)
    (hx0 : int256 x ≠ 0) (hW : WideRegion x)
    (hlive : 2 ≤ int256 (mulShiftTree y x)) :
    0 ≤ int256 (mulMagnitudeTree y x) ∧
      int256 (mulMagnitudeTree y x) < 2 ^ 127 ∧
      (int256 (mulMagnitudeTree y x) : Real) ≤ mulExpRayMagnitudeTarget (int256 y) (int256 x) ∧
      mulExpRayMagnitudeTarget (int256 y) (int256 x) <
        (int256 (mulMagnitudeTree y x) : Real) + 2 := by
  -- the dynamic scale is live: 2^125 ≤ scale ≤ kernelScaleMax
  have hpos : 1 ≤ absTree y := absTree_pos hy hy0
  have hslo : 2 ^ 125 ≤ mulScaleTree y := mulScaleTree_lower hy hpos habs
  obtain ⟨hs256, hscale_eq, hshi⟩ := mulScaleTree_spec hy habs
  -- quotient bounds at the dynamic scale
  have hr0eq : r0MulTree y x = r0ScaledTree (mulScaleTree y) x := r0MulTree_eq_scaled y x
  obtain ⟨hr0lo, hr0hi⟩ := r0Scaled_bounds hslo hshi hx hW
  rw [← hr0eq] at hr0lo hr0hi
  have hr0w : r0MulTree y x < 2 ^ 256 := r0MulTree_lt y x
  have hr0nn : 0 ≤ int256 (r0MulTree y x) := le_trans (by positivity) hr0lo
  obtain ⟨hr0i, hr0255⟩ := int256_eq_of_nonneg hr0w hr0nn
  have hr0nat1 : 1 ≤ r0MulTree y x := by
    have h : (1 : Int) ≤ ((r0MulTree y x : Nat) : Int) := by
      rw [← hr0i]
      calc (1:Int) ≤ 2 ^ 123 := by norm_num
        _ ≤ int256 (r0MulTree y x) := hr0lo
    exact_mod_cast h
  -- the decremented quotient word
  have hsub : evmSub (r0MulTree y x) marginWord = r0MulTree y x - 1 := by
    unfold marginWord
    exact evmSub_small hr0nat1 hr0w
  have hr0nat129 : r0MulTree y x < 2 ^ 129 := by
    have h : ((r0MulTree y x : Nat) : Int) < 2 ^ 129 := by rw [← hr0i]; exact hr0hi
    exact_mod_cast h
  set W := r0MulTree y x - 1 with hWdef
  have hWnat129 : W < 2 ^ 129 := lt_of_le_of_lt (Nat.sub_le _ _) hr0nat129
  have hWw : W < 2 ^ 256 := lt_trans hWnat129 (by norm_num)
  have hWi : int256 W = (W : Int) := int256_of_lt (lt_trans hWnat129 (by norm_num))
  have hWnn : 0 ≤ int256 W := by rw [hWi]; exact Int.natCast_nonneg _
  have hWhi : int256 W < 2 ^ 129 := by
    rw [hWi]
    exact_mod_cast hWnat129
  -- the closing-shift word
  obtain ⟨hsh2, hsh256, hsheq⟩ := mulShift_word_facts hy hx habs hW hlive
  set sh := mulShiftTree y x with hshdef
  -- the magnitude word and its floor sandwich
  have hmag : mulMagnitudeTree y x = evmShr sh W := by
    rw [mulMagnitudeTree_live hx hx0 hW.1, hsub]
  obtain ⟨hfl_lo, hfl_hi⟩ := shr_floor_sandwich (W := W) (s := sh) hsh256 hWw hWnn
  obtain ⟨hm_nn, hm_lt⟩ := mulShr_facts hWw hsh2 (Nat.le_of_lt_succ hsh256) hWnn hWhi
  rw [← hmag] at hfl_lo hfl_hi hm_nn hm_lt
  -- the per-point brackets at the dynamic scale
  have hover := r0Scaled_real_over_within hslo hshi hx hW
  have hunder := r0Scaled_real_under_within hslo hshi hx hW
  rw [← hr0eq] at hover hunder
  -- the target fold A·2^sh = scale·exp(rt)
  have htransport := mulShiftTree_transport hy hx habs hW
  have hkS : int256 (kTree x) + ((sh : Nat) : Int) = ((scaleShiftTree (absTree y) : Nat) : Int) := by
    have h1 := hsheq
    rw [htransport] at h1
    linarith [h1]
  have hfold : mulExpRayMagnitudeTarget (int256 y) (int256 x) * ((2 : Real) ^ (sh : Nat)) =
      (mulScaleTree y : Real) * Real.exp (reducedArg x) := by
    unfold mulExpRayMagnitudeTarget
    have hRAY : ((RAY : Nat) : Real) = (10 ^ 27 : Real) := by unfold RAY; push_cast; norm_num
    rw [hRAY, exp_X_over_RAY]
    have hay : ((int256 y).natAbs : Real) = ((absTree y : Nat) : Real) := by
      rw [absTree_eq_natAbs hy]
    have hscaleR : ((mulScaleTree y : Nat) : Real) =
        ((absTree y : Nat) : Real) * (2 : Real) ^ (scaleShiftTree (absTree y) : Nat) := by
      rw [hscale_eq]
      push_cast
      ring
    have hzpow : (2 : Real) ^ (int256 (kTree x)) * (2 : Real) ^ (sh : Nat) =
        (2 : Real) ^ (scaleShiftTree (absTree y) : Nat) := by
      have h1 : (2:Real) ^ (sh : Nat) = (2:Real) ^ (((sh : Nat) : Int)) := (zpow_natCast 2 _).symm
      have h2 : (2:Real) ^ (scaleShiftTree (absTree y) : Nat) =
          (2:Real) ^ (((scaleShiftTree (absTree y) : Nat) : Int)) := (zpow_natCast 2 _).symm
      rw [h1, h2, ← zpow_add₀ (by norm_num : (2:Real) ≠ 0)]
      rw [hkS]
    rw [hay, hscaleR, ← hzpow]
    ring
  -- the sandwich in Real form
  have hshpowpos : (0:Real) < (2 : Real) ^ (sh : Nat) := by positivity
  have hWR : (int256 W : Real) = (int256 (r0MulTree y x) : Real) - 1 := by
    rw [hWi, hr0i]
    have h2 : ((W : Nat) : Int) = ((r0MulTree y x : Nat) : Int) - 1 := by
      rw [hWdef]
      exact Int.ofNat_sub hr0nat1
    rw [h2]
    push_cast
    ring
  have hfl_loR : ((2 : Real) ^ (sh : Nat)) * (int256 (mulMagnitudeTree y x) : Real) ≤
      (int256 (r0MulTree y x) : Real) - 1 := by
    have h := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hfl_lo
    push_cast at h
    rw [← hWR]
    linarith [h]
  have hfl_hiR : (int256 (r0MulTree y x) : Real) - 1 <
      ((2 : Real) ^ (sh : Nat)) * (int256 (mulMagnitudeTree y x) : Real) +
        (2 : Real) ^ (sh : Nat) := by
    have h := (@Int.cast_lt Real _ _ _ _ _ _ _).mpr hfl_hi
    push_cast at h
    rw [← hWR]
    linarith [h]
  have hBlt1 :
      (2 * 4668745981919039833 / 10000000000000000000 : Real) < 1 :=
    over_budget_image_lt_one
  have h4 : (4:Real) ≤ (2 : Real) ^ (sh : Nat) := by
    calc (4:Real) = (2:Real) ^ (2:Nat) := by norm_num
      _ ≤ (2 : Real) ^ (sh : Nat) := by
        apply pow_le_pow_right₀ (by norm_num)
        exact hsh2
  refine ⟨hm_nn, hm_lt, ?_, ?_⟩
  · -- over side: 2^sh·m ≤ r0 − 1 < scale·exp(rt) = A·2^sh, so m < A
    have hchain : (int256 (mulMagnitudeTree y x) : Real) * ((2 : Real) ^ (sh : Nat)) <
        mulExpRayMagnitudeTarget (int256 y) (int256 x) * ((2 : Real) ^ (sh : Nat)) := by
      rw [hfold]
      linarith [hfl_loR, hover, hBlt1]
    exact le_of_lt ((mul_lt_mul_right hshpowpos).mp hchain)
  · -- under side: A·2^sh = scale·exp(rt) ≤ r0 + 2993/1000 < (m + 2)·2^sh at two bits of shift
    have hchain : mulExpRayMagnitudeTarget (int256 y) (int256 x) * ((2 : Real) ^ (sh : Nat)) <
        ((int256 (mulMagnitudeTree y x) : Real) + 2) * ((2 : Real) ^ (sh : Nat)) := by
      rw [hfold]
      linarith [hfl_hiR, hunder, h4]
    exact (mul_lt_mul_right hshpowpos).mp hchain

/-! ## Sign application -/

/-- Live-region signed bracket for the tree result. -/
theorem mulExpTree_bracket_live {y x : Nat} (hy : y < 2 ^ 256) (hx : x < 2 ^ 256)
    (hy0 : y ≠ 0) (habs : absTree y ≤ kernelScaleMax)
    (hx0 : int256 x ≠ 0) (hW : WideRegion x)
    (hlive : 2 ≤ int256 (mulShiftTree y x)) :
    MulExpRayBracket (int256 y) (int256 x) (int256 (mulExpTree y x)) := by
  obtain ⟨hm0, hmlt, hmle, hmlt2⟩ := mulMagnitude_bracket_live hy hx hy0 habs hx0 hW hlive
  have hmagw : mulMagnitudeTree y x < 2 ^ 256 := mulMagnitudeTree_lt y x
  obtain ⟨hmi, hm255⟩ := int256_eq_of_nonneg hmagw hm0
  by_cases hneg : y < 2 ^ 255
  · have hypos : 0 < y := Nat.pos_of_ne_zero hy0
    have hynn : ¬ (int256 y < 0) := by
      have : int256 y = (y : Int) := int256_of_lt hneg
      rw [this]
      exact not_lt.mpr (Int.natCast_nonneg y)
    rw [mulExpTree_pos hypos hneg]
    unfold MulExpRayBracket
    rw [if_neg hynn]
    exact ⟨hm0, hmle, hmlt2⟩
  · have hlo : 2 ^ 255 ≤ y := by omega
    have hyneg : int256 y < 0 := by
      unfold int256
      rw [if_neg (by omega)]
      have h1 : (y : Int) < 2 ^ 256 := by exact_mod_cast hy
      omega
    rcases Nat.eq_zero_or_pos (mulMagnitudeTree y x) with hmz | hmpos
    · have hzero : mulExpTree y x = 0 := by
        unfold mulExpTree
        rw [hmz]
        unfold evmMul
        rw [u256_self (by norm_num : (0:Nat) < 2 ^ 256)]
        simp [u256, WORD_MOD]
      rw [hzero, int256_zero_word]
      unfold MulExpRayBracket
      rw [if_pos hyneg]
      have hmz' : int256 (mulMagnitudeTree y x) = 0 := by rw [hmz]; exact int256_zero_word
      rw [hmz'] at hmle hmlt2
      exact ⟨le_refl 0, by simpa using hmle, by rw [neg_zero]; simpa using hmlt2⟩
    · rw [mulExpTree_negative hlo hy hmpos]
      have hmnat255 : mulMagnitudeTree y x < 2 ^ 255 := by
        have h : ((mulMagnitudeTree y x : Nat) : Int) < 2 ^ 127 := by rw [← hmi]; exact hmlt
        have h' : mulMagnitudeTree y x < 2 ^ 127 := by exact_mod_cast h
        have : (2:Nat) ^ 127 < 2 ^ 255 := by norm_num
        omega
      have hres : int256 (2 ^ 256 - mulMagnitudeTree y x) = -(int256 (mulMagnitudeTree y x)) := by
        unfold int256
        rw [if_neg (by omega), if_pos hmnat255]
        have h1 : ((2 ^ 256 - mulMagnitudeTree y x : Nat) : Int) =
            2 ^ 256 - ((mulMagnitudeTree y x : Nat) : Int) := by
          push_cast
          omega
        rw [h1]
        ring
      rw [hres]
      unfold MulExpRayBracket
      rw [if_pos hyneg, neg_neg]
      exact ⟨hm0, hmle, hmlt2⟩

/-! ## Result range -/

theorem mulExpTree_int128_range_live {y x : Nat} (hy : y < 2 ^ 256) (hx : x < 2 ^ 256)
    (hy0 : y ≠ 0) (habs : absTree y ≤ kernelScaleMax)
    (hx0 : int256 x ≠ 0) (hW : WideRegion x)
    (hlive : 2 ≤ int256 (mulShiftTree y x)) :
    -(2 ^ 127 : Int) ≤ int256 (mulExpTree y x) ∧
      int256 (mulExpTree y x) < 2 ^ 127 := by
  obtain ⟨hm0, hmlt, _, _⟩ := mulMagnitude_bracket_live hy hx hy0 habs hx0 hW hlive
  have hmagw : mulMagnitudeTree y x < 2 ^ 256 := mulMagnitudeTree_lt y x
  obtain ⟨hmi, _⟩ := int256_eq_of_nonneg hmagw hm0
  have hmnat127 : mulMagnitudeTree y x < 2 ^ 127 := by
    have h : ((mulMagnitudeTree y x : Nat) : Int) < 2 ^ 127 := by
      rw [← hmi]
      exact hmlt
    exact_mod_cast h
  by_cases hneg : y < 2 ^ 255
  · rw [mulExpTree_pos (Nat.pos_of_ne_zero hy0) hneg]
    exact ⟨by omega, hmlt⟩
  · have hlo : 2 ^ 255 ≤ y := by omega
    rcases Nat.eq_zero_or_pos (mulMagnitudeTree y x) with hmz | hmpos
    · have hzero : mulExpTree y x = 0 := by
        unfold mulExpTree
        rw [hmz]
        unfold evmMul
        rw [u256_self (by norm_num : (0 : Nat) < 2 ^ 256)]
        simp [u256, WORD_MOD]
      rw [hzero, int256_zero_word]
      norm_num
    · rw [mulExpTree_negative hlo hy hmpos]
      have hres : int256 (2 ^ 256 - mulMagnitudeTree y x) =
          -(int256 (mulMagnitudeTree y x)) := by
        unfold int256
        rw [if_neg (by omega), if_pos (lt_trans hmnat127 (by norm_num))]
        omega
      rw [hres]
      constructor
      · exact neg_le_neg (le_of_lt hmlt)
      · exact lt_of_le_of_lt (neg_nonpos.mpr hm0) (by norm_num)

theorem mulExpTree_int128_range {y x : Nat} (h : MulExpRayValueDomain y x) :
    -(2 ^ 127 : Int) ≤ int256 (mulExpTree y x) ∧
      int256 (mulExpTree y x) < 2 ^ 127 := by
  obtain ⟨⟨hy, hx⟩, hxhi, hlive⟩ := h
  have habs : absTree y ≤ kernelScaleMax := absTree_le_kernelScaleMax_of_int128Word hy
  rcases Nat.eq_zero_or_pos y with hy0 | hypos
  · subst hy0
    rw [mulExpTree_zero, int256_zero_word]
    norm_num
  by_cases hclamp : int256 x ≤ int256 mulExpRayZeroMax
  · rw [mulExpTree_clamped hx hclamp, int256_zero_word]
    norm_num
  by_cases hx0 : int256 x = 0
  · have hxw0 : x = 0 := (int256_zero_iff_of_canonical hx).mp hx0
    subst hxw0
    rw [mulExpTree_scale_point hy.1 habs]
    exact int256_range_of_signextend_15_eq_self hy.1 hy.2
  · exact mulExpTree_int128_range_live hy.1 hx (by omega) habs hx0
      ⟨by omega, hxhi⟩ hlive

theorem mulExpTree_int128_word {y x : Nat} (h : MulExpRayValueDomain y x) :
    Int128Word (mulExpTree y x) := by
  have hrange := mulExpTree_int128_range h
  have hword := mulExpTree_lt y x
  exact ⟨hword, signextend_15_eq_self_of_int256_range hword hrange.1 hrange.2⟩

theorem run_mul_exp_ray_evm_eq_tree {y x : Nat} (h : MulExpRayValueDomain y x) :
    run_mul_exp_ray_evm y x = .ok (mulExpTree y x) :=
  run_mul_exp_ray_evm_eq_tree_of_guard y x h.1.1.2 (mulExpTree_int128_word h).2
    ((valueDomain_iff_guard_eq_zero h.1).mp h)

/-! ## The bracket on the whole value domain -/

/-- **The public runtime bracket on the value domain.** Every accepted input returns a result
satisfying the signed two-unit magnitude bracket. -/
theorem mulExpRay_run_bracket {y x : Nat} (h : MulExpRayValueDomain y x) :
    MulExpRayRunBracket y x := by
  obtain ⟨⟨hy, hx⟩, hxhi, hlive⟩ := h
  have habs : absTree y ≤ kernelScaleMax := absTree_le_kernelScaleMax_of_int128Word hy
  rcases Nat.eq_zero_or_pos y with hy0 | hypos
  · subst hy0
    exact mulExpRay_run_bracket_zero x
      ((valueDomain_iff_guard_eq_zero ⟨hy, hx⟩).mp ⟨⟨hy, hx⟩, hxhi, hlive⟩)
  by_cases hclamp : int256 x ≤ int256 mulExpRayZeroMax
  · exact mulExpRay_run_bracket_clamped hy hx habs hlive hclamp
  by_cases hx0 : int256 x = 0
  · have hxw0 : x = 0 := by
      have h := (int256_zero_iff_of_canonical hx).1 hx0
      exact h
    subst hxw0
    exact mulExpRay_run_bracket_scale_point hy habs hlive
  · -- the live region
    have hWx : WideRegion x := ⟨by omega, hxhi⟩
    have hrun : run_mul_exp_ray_evm y x = .ok (mulExpTree y x) :=
      run_mul_exp_ray_evm_eq_tree ⟨⟨hy, hx⟩, hxhi, hlive⟩
    exact ⟨mulExpTree y x, hrun,
      mulExpTree_bracket_live hy.1 hx (by omega) habs hx0 hWx hlive⟩

/-! ## Floor membership and the small-target pin -/

/-- The bracketed magnitude is the floor of the target or one below it. -/
theorem mulExpRayMagnitudeBracket_mem_floor {y x m : Int}
    (h : MulExpRayMagnitudeBracket y x m) :
    m = ⌊mulExpRayMagnitudeTarget y x⌋ ∨ m = ⌊mulExpRayMagnitudeTarget y x⌋ - 1 := by
  obtain ⟨hm0, hle, hlt⟩ := h
  have h1 : m ≤ ⌊mulExpRayMagnitudeTarget y x⌋ := Int.le_floor.mpr hle
  have h2 : ⌊mulExpRayMagnitudeTarget y x⌋ < m + 2 := by
    rw [Int.floor_lt]
    push_cast
    exact hlt
  omega

/-- A target below one output unit pins the bracketed magnitude to zero. -/
theorem mulExpRayMagnitudeBracket_pins_zero {y x m : Int}
    (h : MulExpRayMagnitudeBracket y x m)
    (hA : mulExpRayMagnitudeTarget y x < 1) : m = 0 := by
  obtain ⟨hm0, hle, _⟩ := h
  have h1 : (m : Real) < 1 := lt_of_le_of_lt hle hA
  have h2 : m < 1 := by exact_mod_cast h1
  omega

/-- **Floor membership on the value domain.** Every accepted input's result magnitude is `⌊A⌋`
or `⌊A⌋ − 1`. -/
theorem mulExpRay_run_floor_membership {y x : Nat} (h : MulExpRayValueDomain y x) :
    ∃ r, run_mul_exp_ray_evm y x = .ok r ∧
      ((if int256 y < 0 then -(int256 r) else int256 r) =
          ⌊mulExpRayMagnitudeTarget (int256 y) (int256 x)⌋ ∨
        (if int256 y < 0 then -(int256 r) else int256 r) =
          ⌊mulExpRayMagnitudeTarget (int256 y) (int256 x)⌋ - 1) := by
  obtain ⟨r, hrun, hbracket⟩ := mulExpRay_run_bracket h
  refine ⟨r, hrun, ?_⟩
  unfold MulExpRayBracket at hbracket
  split_ifs with hneg
  · rw [if_pos hneg] at hbracket
    exact mulExpRayMagnitudeBracket_mem_floor hbracket
  · rw [if_neg hneg] at hbracket
    exact mulExpRayMagnitudeBracket_mem_floor hbracket

/-- **The small-target pin on the value domain.** A target magnitude below one output unit
forces a zero result. -/
theorem mulExpRay_run_pins_zero {y x : Nat} (h : MulExpRayValueDomain y x)
    (hA : mulExpRayMagnitudeTarget (int256 y) (int256 x) < 1) :
    run_mul_exp_ray_evm y x = .ok 0 ∨
      ∃ r, run_mul_exp_ray_evm y x = .ok r ∧ int256 r = 0 := by
  obtain ⟨r, hrun, hbracket⟩ := mulExpRay_run_bracket h
  unfold MulExpRayBracket at hbracket
  right
  refine ⟨r, hrun, ?_⟩
  split_ifs at hbracket with hneg
  · have := mulExpRayMagnitudeBracket_pins_zero hbracket hA
    omega
  · exact mulExpRayMagnitudeBracket_pins_zero hbracket hA

end

end ExpYul
