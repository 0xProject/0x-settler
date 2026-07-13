import ExpProof.Mul
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# `mulExpRay` shell regions: the scale point and the zero clamp

Two accepted subdomains admit exact results without the polynomial certificates: at `x = 0` the
kernel's rational is exactly one and the pin returns the magnitude unchanged, and at or below the
zero cutoff the clamp returns zero, which stays inside the bracket because every supported
magnitude times `exp(x/10²⁷)` is below one there.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word
open ExpRealSpec

set_option maxRecDepth 100000

/-! ## Word plumbing -/

private theorem u256_self {a : Nat} (h : a < 2 ^ 256) : u256 a = a := u256_of_lt_pow256 h

private theorem evmSub_small {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 256) :
    evmSub a b = a - b := by
  unfold evmSub
  rw [u256_self ha, u256_self (lt_of_le_of_lt hb ha)]
  unfold u256 WORD_MOD
  omega

private theorem evmAdd_small {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : a + b < 2 ^ 256) : evmAdd a b = a + b := by
  unfold evmAdd
  rw [u256_self ha, u256_self hb]
  unfold u256 WORD_MOD
  omega

private theorem evmMul_small {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : a * b < 2 ^ 256) : evmMul a b = a * b := by
  unfold evmMul
  rw [u256_self ha, u256_self hb]
  unfold u256 WORD_MOD
  omega

private theorem evmShl_small {s v : Nat} (hs : s < 256) (hv : v < 2 ^ 256)
    (h : v * 2 ^ s < 2 ^ 256) : evmShl s v = v * 2 ^ s := by
  unfold evmShl
  rw [u256_self (lt_trans hs (by norm_num)), u256_self hv, if_pos hs]
  unfold u256 WORD_MOD
  omega

private theorem evmShr_small {s v : Nat} (hs : s < 256) (hv : v < 2 ^ 256) :
    evmShr s v = v / 2 ^ s := by
  unfold evmShr
  rw [u256_self (lt_trans hs (by norm_num)), u256_self hv, if_pos hs]

private theorem evmDiv_exact {a b : Nat} (hb : 0 < b) (ha : a < 2 ^ 256) (hbw : b < 2 ^ 256)
    (hab : a * b < 2 ^ 256) : evmDiv (evmMul a b) b = a := by
  rw [evmMul_small ha hbw hab]
  simp only [evmDiv, u256_self hab, u256_self hbw]
  rw [if_neg (by omega : ¬ b = 0)]
  exact Nat.mul_div_cancel _ hb

/-- Xor against a low mask complements below the mask. -/
private theorem xor_all_ones : ∀ (k y : Nat), y < 2 ^ k → y ^^^ (2 ^ k - 1) = 2 ^ k - 1 - y := by
  intro k
  induction k with
  | zero =>
    intro y hy
    have hy0 : y = 0 := by omega
    subst hy0
    rfl
  | succ n ih =>
    intro y hy
    have hp : (2 : Nat) ^ (n + 1) = 2 * 2 ^ n := by ring
    have hpos : (0 : Nat) < 2 ^ n := Nat.two_pow_pos n
    have hdiv : (y ^^^ (2 ^ (n + 1) - 1)) / 2 = (y / 2) ^^^ (2 ^ n - 1) := by
      have h1 : (y ^^^ (2 ^ (n + 1) - 1)) >>> 1 = (y >>> 1) ^^^ ((2 ^ (n + 1) - 1) >>> 1) :=
        Nat.shiftRight_xor_distrib
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at h1
      rw [show (2 ^ (n + 1) - 1) / 2 ^ 1 = 2 ^ n - 1 by omega] at h1
      simpa using h1
    have hmod : (y ^^^ (2 ^ (n + 1) - 1)) % 2 = (y + (2 ^ (n + 1) - 1)) % 2 :=
      Nat.xor_mod_two_eq
    have hih := ih (y / 2) (by omega)
    have hsplit := Nat.div_add_mod (y ^^^ (2 ^ (n + 1) - 1)) 2
    have hysplit := Nat.div_add_mod y 2
    omega

/-! ## Sign and magnitude semantics of the tree -/

theorem signTree_nonneg {y : Nat} (hy : y < 2 ^ 255) : signTree y = 0 := by
  unfold signTree evmSar
  rw [u256_self (by norm_num : (255 : Nat) < 2 ^ 256), u256_self (lt_trans hy (by norm_num))]
  rw [if_neg (by omega), if_neg (by omega)]
  exact Nat.div_eq_of_lt (by omega)

theorem signTree_neg {y : Nat} (hlo : 2 ^ 255 ≤ y) (hy : y < 2 ^ 256) :
    signTree y = 2 ^ 256 - 1 := by
  unfold signTree evmSar
  rw [u256_self (by norm_num : (255 : Nat) < 2 ^ 256), u256_self hy]
  rw [if_pos (by omega), if_neg (by omega)]
  unfold WORD_MOD
  rw [Nat.div_eq_of_lt (by omega)]
  omega

theorem absTree_nonneg {y : Nat} (hy : y < 2 ^ 255) : absTree y = y := by
  unfold absTree
  rw [signTree_nonneg hy]
  unfold Common.Word.evmXor
  rw [u256_self (lt_trans hy (by norm_num)), u256_self (by norm_num : (0 : Nat) < 2 ^ 256)]
  rw [Nat.xor_zero]
  exact evmSub_small (by omega) (lt_trans hy (by norm_num))

theorem absTree_neg {y : Nat} (hlo : 2 ^ 255 ≤ y) (hy : y < 2 ^ 256) :
    absTree y = 2 ^ 256 - y := by
  unfold absTree
  rw [signTree_neg hlo hy]
  unfold Common.Word.evmXor
  rw [u256_self hy, u256_self (by norm_num : 2 ^ 256 - 1 < 2 ^ 256)]
  rw [xor_all_ones 256 y hy]
  unfold evmSub
  rw [u256_self (by omega : 2 ^ 256 - 1 - y < 2 ^ 256),
    u256_self (by norm_num : 2 ^ 256 - 1 < 2 ^ 256)]
  unfold u256 WORD_MOD
  omega

/-- The magnitude word is the absolute value of the signed interpretation. -/
theorem absTree_eq_natAbs {y : Nat} (hy : y < 2 ^ 256) :
    absTree y = (int256 y).natAbs := by
  by_cases hsign : y < 2 ^ 255
  · rw [absTree_nonneg hsign]
    unfold int256
    rw [if_pos hsign]
    exact (Int.natAbs_natCast y).symm
  · rw [absTree_neg (by omega) hy]
    unfold int256
    rw [if_neg hsign]
    have hyi : (y : Int) < 2 ^ 256 := by exact_mod_cast hy
    have hyl : (2 ^ 255 : Int) ≤ (y : Int) := by exact_mod_cast (by omega : 2 ^ 255 ≤ y)
    omega

theorem absTree_le_kernelScaleMax_of_int128Word {y : Nat} (hy : Int128Word y) :
    absTree y ≤ kernelScaleMax := by
  rw [absTree_eq_natAbs hy.1, kernelScaleMax_eq]
  obtain ⟨hlo, hhi⟩ := int256_range_of_signextend_15_eq_self hy.1 hy.2
  by_cases hneg : int256 y < 0
  · have hnatI : (((int256 y).natAbs : Nat) : Int) ≤ 2 ^ 127 := by
      rw [Int.ofNat_natAbs_of_nonpos (le_of_lt hneg)]
      exact neg_le_neg hlo
    exact_mod_cast hnatI
  · have hnatI : (((int256 y).natAbs : Nat) : Int) ≤ 2 ^ 127 := by
      rw [Int.natAbs_of_nonneg (not_lt.mp hneg)]
      exact le_of_lt hhi
    exact_mod_cast hnatI

theorem sgnTree_pos {y : Nat} (hpos : 0 < y) (hy : y < 2 ^ 255) : sgnTree y = 1 := by
  unfold sgnTree
  rw [signTree_nonneg hy, absTree_nonneg hy]
  unfold evmLt evmOr
  rw [u256_self (by norm_num : (0 : Nat) < 2 ^ 256), u256_self (lt_trans hy (by norm_num))]
  rw [if_pos hpos]
  norm_num [u256, WORD_MOD]

theorem sgnTree_neg {y : Nat} (hlo : 2 ^ 255 ≤ y) (hy : y < 2 ^ 256) :
    sgnTree y = 2 ^ 256 - 1 := by
  unfold sgnTree
  rw [signTree_neg hlo hy]
  have hb : evmLt 0 (absTree y) < 2 ^ 256 := by
    unfold evmLt
    split_ifs <;> norm_num
  unfold evmOr
  rw [u256_self (by norm_num : 2 ^ 256 - 1 < 2 ^ 256), u256_self hb]
  have h1 : (2 ^ 256 - 1 : Nat) ≤ (2 ^ 256 - 1) ||| evmLt 0 (absTree y) := Nat.left_le_or
  have h2 : (2 ^ 256 - 1 : Nat) ||| evmLt 0 (absTree y) < 2 ^ 256 :=
    Nat.or_lt_two_pow (by norm_num) hb
  omega

/-- With a positive multiplier, the result word is the kernel magnitude. -/
theorem mulExpTree_pos {y x : Nat} (hpos : 0 < y) (hy : y < 2 ^ 255) :
    mulExpTree y x = mulMagnitudeTree y x := by
  unfold mulExpTree
  rw [sgnTree_pos hpos hy]
  rw [evmMul_small (mulMagnitudeTree_lt y x) (by norm_num) (by
    have := mulMagnitudeTree_lt y x; omega)]
  omega

/-- With a negative multiplier and a positive magnitude, the result word is its negation. -/
theorem mulExpTree_negative {y x : Nat} (hlo : 2 ^ 255 ≤ y) (hy : y < 2 ^ 256)
    (hm : 0 < mulMagnitudeTree y x) :
    mulExpTree y x = 2 ^ 256 - mulMagnitudeTree y x := by
  unfold mulExpTree
  rw [sgnTree_neg hlo hy]
  have hmlt : mulMagnitudeTree y x < 2 ^ 256 := mulMagnitudeTree_lt y x
  unfold evmMul
  rw [u256_self hmlt, u256_self (by norm_num : 2 ^ 256 - 1 < 2 ^ 256)]
  obtain ⟨k, hk⟩ : ∃ k, mulMagnitudeTree y x = k + 1 := ⟨mulMagnitudeTree y x - 1, by omega⟩
  rw [hk] at hmlt ⊢
  have key : (k + 1) * (2 ^ 256 - 1) = k * 2 ^ 256 + (2 ^ 256 - (k + 1)) := by
    have h2 : (0 : Nat) < 2 ^ 256 := by norm_num
    omega
  rw [key]
  unfold u256 WORD_MOD
  rw [Nat.add_comm (k * 2 ^ 256), Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt (by omega)

/-! ## The scale headroom realizes the scale exactly -/

theorem mulScaleTree_spec {y : Nat} (_hy : y < 2 ^ 256)
    (habs : absTree y ≤ kernelScaleMax) :
    scaleShiftTree (absTree y) ≤ 127 ∧
      mulScaleTree y = absTree y * 2 ^ scaleShiftTree (absTree y) ∧
      mulScaleTree y ≤ kernelScaleMax := by
  have haylt : absTree y < 2 ^ 256 := absTree_lt y
  rcases Nat.eq_zero_or_pos (absTree y) with h0 | hpos
  · have hclz : evmClz 0 = 256 := by
      unfold evmClz
      rw [u256_self (by norm_num)]
      simp
    have hs : evmSub 256 scaleClzBias = 127 := by
      rw [evmSub_small (by unfold scaleClzBias; omega) (by norm_num)]
      unfold scaleClzBias
      norm_num
    have hsst : scaleShiftTree (absTree y) = 127 := by
      rw [h0]
      unfold scaleShiftTree
      rw [hclz, hs]
      norm_num [evmShr, evmAdd, u256, WORD_MOD]
    have hshl : evmShl 127 (0 : Nat) = 0 := by
      rw [evmShl_small (by norm_num) (by norm_num) (by norm_num)]
      ring
    have hscale : mulScaleTree y = 0 := by
      unfold mulScaleTree
      rw [hsst, h0, hshl]
    rw [hsst, hscale, h0]
    exact ⟨by norm_num, by ring, Nat.zero_le _⟩
  · by_cases hend : absTree y = kernelScaleMax
    · have hs : scaleShiftTree (absTree y) = 0 := by
        rw [hend, kernelScaleMax_eq]
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
        norm_num [evmAdd, u256, WORD_MOD]
      have hscale : mulScaleTree y = kernelScaleMax := by
        unfold mulScaleTree
        rw [hs, hend]
        norm_num [evmShl, u256, WORD_MOD]
      rw [hs, hscale]
      exact ⟨by norm_num, by rw [hend, kernelScaleMax_eq]; norm_num, le_refl _⟩
    · have hay127 : absTree y < 2 ^ 127 := by
        rw [← kernelScaleMax_eq]
        omega
      have hlog : Nat.log2 (absTree y) ≤ 126 := by
        have h1 : 2 ^ Nat.log2 (absTree y) ≤ absTree y :=
          Nat.log2_self_le (by omega)
        by_contra h
        push_neg at h
        have h2 : (2 : Nat) ^ 127 ≤ 2 ^ Nat.log2 (absTree y) :=
          Nat.pow_le_pow_right (by norm_num) h
        omega
      have hlt : absTree y < 2 ^ (Nat.log2 (absTree y) + 1) :=
        Nat.lt_log2_self
      have hclz : evmClz (absTree y) = 255 - Nat.log2 (absTree y) := by
        unfold evmClz
        rw [u256_self haylt, if_neg (by omega)]
      have hshr : evmShr 127 (absTree y) = 0 := by
        unfold evmShr
        rw [u256_self (by norm_num), u256_self haylt, if_pos (by norm_num)]
        exact Nat.div_eq_of_lt hay127
      have hs : scaleShiftTree (absTree y) = 126 - Nat.log2 (absTree y) := by
        unfold scaleShiftTree
        have hsub : evmSub (255 - Nat.log2 (absTree y)) scaleClzBias =
            126 - Nat.log2 (absTree y) := by
          rw [evmSub_small (by unfold scaleClzBias; omega) (by omega)]
          unfold scaleClzBias
          omega
        rw [hclz, hshr, hsub]
        unfold evmAdd
        have hshiftlt : 126 - Nat.log2 (absTree y) < 2 ^ 256 := by
          exact lt_of_le_of_lt (Nat.sub_le _ _) (by norm_num)
        rw [show u256 (126 - Nat.log2 (absTree y)) = 126 - Nat.log2 (absTree y) from
          u256_self hshiftlt, show u256 0 = 0 from u256_self (by norm_num)]
        rw [Nat.add_zero, u256_self hshiftlt]
      have hfit : absTree y * 2 ^ (126 - Nat.log2 (absTree y)) < 2 ^ 127 := by
        calc absTree y * 2 ^ (126 - Nat.log2 (absTree y))
            < 2 ^ (Nat.log2 (absTree y) + 1) *
                2 ^ (126 - Nat.log2 (absTree y)) :=
              mul_lt_mul_of_pos_right hlt (Nat.two_pow_pos _)
          _ = 2 ^ (Nat.log2 (absTree y) + 1 +
                (126 - Nat.log2 (absTree y))) := by
              rw [← pow_add]
          _ ≤ 2 ^ 127 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hshl : evmShl (126 - Nat.log2 (absTree y)) (absTree y) =
          absTree y * 2 ^ (126 - Nat.log2 (absTree y)) :=
        evmShl_small (by omega) haylt (lt_trans hfit (by norm_num))
      have hscale : mulScaleTree y =
          absTree y * 2 ^ (126 - Nat.log2 (absTree y)) := by
        unfold mulScaleTree
        rw [hs, hshl]
      rw [hs, hscale]
      refine ⟨by omega, rfl, ?_⟩
      rw [kernelScaleMax_eq]
      omega
/-! ## The scale point `x = 0` -/

private theorem kTree_zero : kTree 0 = 0 := by
  unfold kTree kRoundShift kHalfShift cInvQ192
  norm_num [evmSar, evmAdd, evmShl, evmMul, u256, WORD_MOD]

private theorem tTree_zero : tTree 0 = 0 := by
  unfold tTree tArgShift k27Q235 ln2Q235
  rw [kTree_zero]
  norm_num [evmSar, evmSub, evmMul, u256, WORD_MOD]

private theorem vTree_zero : vTree 0 = 0 := by
  unfold vTree squareShift
  rw [tTree_zero]
  norm_num [evmShr, evmMul, u256, WORD_MOD]

private theorem evTree_zero : evTree 0 = ev4 := by
  unfold evTree ev0 ev1 ev2 ev3 ev4 evShift1 evShift2 evShift3 evShift4
  rw [vTree_zero]
  norm_num [evmAdd, evmShr, evmMul, u256, WORD_MOD]

private theorem odTree_zero : odTree 0 = od4 := by
  unfold odTree od0 od1 od2 od3 od4 odShift1 odShift2 odShift3 odShift4
  rw [vTree_zero]
  norm_num [evmAdd, evmShr, evmMul, u256, WORD_MOD]

private theorem todTree_zero : todTree 0 = 0 := by
  unfold todTree todShift
  rw [tTree_zero]
  norm_num [evmSar, evmMul, u256, WORD_MOD]

private theorem r0MulTree_scale_point {y : Nat} (hy : y < 2 ^ 256)
    (habs : absTree y ≤ kernelScaleMax) : r0MulTree y 0 = mulScaleTree y := by
  obtain ⟨_, _, hcap⟩ := mulScaleTree_spec hy habs
  unfold r0MulTree
  have hnum : evmAdd (evTree 0) (todTree 0) = ev4 := by
    rw [evTree_zero, todTree_zero]
    exact evmAdd_small (by unfold ev4; norm_num) (by norm_num) (by unfold ev4; norm_num)
  have hden : evmSub (evTree 0) (todTree 0) = ev4 := by
    rw [evTree_zero, todTree_zero]
    have := evmSub_small (Nat.zero_le ev4) (by unfold ev4; norm_num)
    simpa using this
  rw [hnum, hden]
  exact evmDiv_exact (by unfold ev4; norm_num) (mulScaleTree_lt y) (by unfold ev4; norm_num)
    (by
      calc mulScaleTree y * ev4 ≤ kernelScaleMax * ev4 := Nat.mul_le_mul_right _ hcap
        _ < 2 ^ 256 := by unfold kernelScaleMax ev4; norm_num)

private theorem mulShiftTree_scale_point (y : Nat) :
    mulShiftTree y 0 = scaleShiftTree (absTree y) := by
  unfold mulShiftTree
  rw [kTree_zero, evmSub_small (Nat.zero_le _) (scaleShiftTree_lt _)]
  omega

theorem mulMagnitudeTree_scale_point {y : Nat} (hy : y < 2 ^ 256)
    (hpos : 0 < absTree y) (habs : absTree y ≤ kernelScaleMax) :
    mulMagnitudeTree y 0 = absTree y := by
  obtain ⟨hs256, hscale, hcap⟩ := mulScaleTree_spec hy habs
  have hQlt : kernelScaleMax < 2 ^ 256 := by unfold kernelScaleMax; norm_num
  have hscalepos : 0 < mulScaleTree y := by
    rw [hscale]
    exact Nat.mul_pos hpos (Nat.two_pow_pos _)
  have hslt : evmSlt mulExpRayZeroMax 0 = 1 := by
    rw [evmSlt_eq_ite]
    rw [u256_self mulExpRayZeroMax_lt, u256_self (by norm_num)]
    rw [if_pos (by
      rw [int256_mulExpRayZeroMax]
      unfold int256
      norm_num)]
  have hisz : evmIszero (0 : Nat) = 1 := by
    unfold evmIszero
    rw [u256_self (by norm_num)]
    simp
  unfold mulMagnitudeTree marginWord
  rw [hslt, hisz, r0MulTree_scale_point hy habs, mulShiftTree_scale_point y]
  have haylt : absTree y < 2 ^ 256 := absTree_lt y
  have hsub : evmSub (mulScaleTree y) 1 =
      absTree y * 2 ^ scaleShiftTree (absTree y) - 1 := by
    rw [hscale]
    exact evmSub_small (Nat.mul_pos hpos (Nat.two_pow_pos _)) (by omega)
  rw [hsub]
  have hshr : evmShr (scaleShiftTree (absTree y))
      (absTree y * 2 ^ scaleShiftTree (absTree y) - 1) = absTree y - 1 := by
    rw [evmShr_small (by omega) (by omega)]
    generalize scaleShiftTree (absTree y) = S
    obtain ⟨k, hk⟩ : ∃ k, absTree y = k + 1 := ⟨absTree y - 1, by omega⟩
    rw [hk]
    have hexp : (k + 1) * 2 ^ S - 1 = 2 ^ S - 1 + 2 ^ S * k := by
      have := Nat.two_pow_pos S
      have hd : (k + 1) * 2 ^ S = 2 ^ S * k + 2 ^ S := by ring
      omega
    rw [hexp, Nat.add_mul_div_left _ _ (Nat.two_pow_pos S),
      Nat.div_eq_of_lt (by have := Nat.two_pow_pos S; omega : 2 ^ S - 1 < 2 ^ S)]
    omega
  rw [hshr]
  have hmul : evmMul 1 (absTree y - 1) = absTree y - 1 := by
    rw [evmMul_small (by norm_num) (by omega) (by omega)]
    omega
  rw [hmul]
  rw [evmAdd_small (by norm_num) (by omega) (by omega)]
  omega

/-- **Scale point (tree).** At `x = 0`, the result word is the multiplier itself. -/
theorem mulExpTree_scale_point {y : Nat} (hy : y < 2 ^ 256)
    (habs : absTree y ≤ kernelScaleMax) :
    mulExpTree y 0 = y := by
  rcases Nat.eq_zero_or_pos y with h0 | hypos
  · subst h0
    exact mulExpTree_zero 0
  · by_cases hneg : y < 2 ^ 255
    · have hpos : 0 < absTree y := by rw [absTree_nonneg hneg]; omega
      rw [mulExpTree_pos hypos hneg, mulMagnitudeTree_scale_point hy hpos habs,
        absTree_nonneg hneg]
    · have hlo : 2 ^ 255 ≤ y := by omega
      have hpos : 0 < absTree y := by rw [absTree_neg hlo hy]; omega
      rw [mulExpTree_negative hlo hy (by rw [mulMagnitudeTree_scale_point hy hpos habs]; omega),
        mulMagnitudeTree_scale_point hy hpos habs, absTree_neg hlo hy]
      omega

/-! ## The zero clamp -/

/-- **Clamp (tree).** At or below the zero cutoff, the result word is zero for every
multiplier: the clamp consults only `x`. -/
theorem mulExpTree_clamped {y x : Nat} (hx : x < 2 ^ 256)
    (hclamp : int256 x ≤ int256 mulExpRayZeroMax) : mulExpTree y x = 0 := by
  have hzm := int256_mulExpRayZeroMax
  have hx0 : x ≠ 0 := by
    intro h
    subst h
    rw [show int256 (0 : Nat) = 0 from by unfold int256; norm_num, hzm] at hclamp
    omega
  have hslt : evmSlt mulExpRayZeroMax x = 0 := by
    rw [evmSlt_eq_ite, u256_self mulExpRayZeroMax_lt, u256_self hx, if_neg (by omega)]
  have hisz : evmIszero x = 0 := by
    unfold evmIszero
    rw [u256_self hx, if_neg hx0]
  unfold mulExpTree mulMagnitudeTree
  rw [hslt, hisz]
  simp [evmMul, evmAdd, u256, WORD_MOD]

/-! ## Run-level shell theorems -/

private theorem int256_zero_word : int256 (0 : Nat) = 0 := by unfold int256; norm_num

/-- **Scale point.** `mulExpRay(y, 0)` returns `y` whenever the two-bit closing-shift guard accepts. -/
theorem run_mul_exp_ray_evm_scale_point {y : Nat} (hy : Int128Word y)
    (habs : absTree y ≤ kernelScaleMax) (hshift : 2 ≤ int256 (mulShiftTree y 0)) :
    run_mul_exp_ray_evm y 0 = .ok y := by
  have hguard : mulExpGuardTree y 0 = 0 := by
    rw [mulExpGuardTree_eq_zero_iff (by norm_num)]
    refine ⟨?_, hshift⟩
    rw [int256_mulExpRayHi, int256_zero_word]
    norm_num
  have hresultClean :
      EvmYul.UInt256.signextend (word 15) (word (mulExpTree y 0)) =
        word (mulExpTree y 0) := by
    rw [mulExpTree_scale_point hy.1 habs]
    exact hy.2
  have h := run_mul_exp_ray_evm_eq_tree_of_guard y 0 hy.2 hresultClean hguard
  rwa [mulExpTree_scale_point hy.1 habs] at h

/-- **Clamp.** An accepted `mulExpRay(y, x)` returns zero at or below the zero cutoff. -/
theorem run_mul_exp_ray_evm_clamped {y x : Nat} (hy : Int128Word y) (hx : x < 2 ^ 256)
    (hshift : 2 ≤ int256 (mulShiftTree y x))
    (hclamp : int256 x ≤ int256 mulExpRayZeroMax) :
    run_mul_exp_ray_evm y x = .ok 0 := by
  have hguard : mulExpGuardTree y x = 0 := by
    rw [mulExpGuardTree_eq_zero_iff hx]
    refine ⟨?_, hshift⟩
    rw [int256_mulExpRayHi]
    rw [int256_mulExpRayZeroMax] at hclamp
    omega
  have hresultClean :
      EvmYul.UInt256.signextend (word 15) (word (mulExpTree y x)) =
        word (mulExpTree y x) := by
    rw [mulExpTree_clamped hx hclamp]
    exact int128Word_zero.2
  have h := run_mul_exp_ray_evm_eq_tree_of_guard y x hy.2 hresultClean hguard
  rwa [mulExpTree_clamped hx hclamp] at h

/-! ## Shell brackets -/

noncomputable section

/-- **Scale-point bracket.** The exact result `y` satisfies the public bracket at `x = 0`. -/
theorem mulExpRay_run_bracket_scale_point {y : Nat} (hy : Int128Word y)
    (habs : absTree y ≤ kernelScaleMax) (hshift : 2 ≤ int256 (mulShiftTree y 0)) :
    MulExpRayRunBracket y 0 := by
  refine ⟨y, run_mul_exp_ray_evm_scale_point hy habs hshift, ?_⟩
  rw [int256_zero_word]
  have hA : mulExpRayMagnitudeTarget (int256 y) 0 = ((int256 y).natAbs : ℝ) := by
    unfold mulExpRayMagnitudeTarget
    norm_num
  unfold MulExpRayBracket
  have habs' : (((int256 y).natAbs : ℕ) : ℝ) = |((int256 y : ℤ) : ℝ)| := by
    rw [Nat.cast_natAbs]
    push_cast
    ring
  split_ifs with hneg
  · have habsneg : |((int256 y : ℤ) : ℝ)| = -((int256 y : ℤ) : ℝ) :=
      abs_of_nonpos (by exact_mod_cast le_of_lt hneg)
    refine ⟨by omega, ?_, ?_⟩
    · rw [hA, habs', habsneg]
      push_cast
      linarith
    · rw [hA, habs', habsneg]
      push_cast
      linarith
  · push_neg at hneg
    have habspos : |((int256 y : ℤ) : ℝ)| = ((int256 y : ℤ) : ℝ) :=
      abs_of_nonneg (by exact_mod_cast hneg)
    refine ⟨hneg, ?_, ?_⟩
    · rw [hA, habs', habspos]
    · rw [hA, habs', habspos]
      linarith

/-- Below the zero cutoff, every supported magnitude's real target is below one. -/
theorem clamped_target_lt_one {y x : Nat} (hy : y < 2 ^ 256) (_hx : x < 2 ^ 256)
    (habs : absTree y ≤ kernelScaleMax) (hclamp : int256 x ≤ int256 mulExpRayZeroMax) :
    mulExpRayMagnitudeTarget (int256 y) (int256 x) < 1 := by
  unfold mulExpRayMagnitudeTarget
  have hRAY : (RAY : ℝ) = 10 ^ 27 := by unfold RAY; push_cast; norm_num
  set z : ℝ := (int256 x : ℝ) / (RAY : ℝ) with hz
  have hzM : z ≤ (-88376265521393026950697095485 : ℝ) / 10 ^ 27 := by
    rw [hz, hRAY]
    apply div_le_div_of_nonneg_right ?_ (by norm_num)
    · exact_mod_cast le_trans hclamp (le_of_eq int256_mulExpRayZeroMax)
  have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hexp1 : Real.exp (z + 127 * Real.log 2) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    nlinarith [hzM, hlog]
  have hpow : (2 : ℝ) ^ (127 : ℕ) * Real.exp z = Real.exp (z + 127 * Real.log 2) := by
    rw [Real.exp_add]
    rw [show (127 : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ (127 : ℕ)) from by
      rw [Real.log_pow]; push_cast; ring]
    rw [Real.exp_log (by positivity)]
    ring
  have hnat : ((int256 y).natAbs : ℝ) ≤ ((kernelScaleMax : Nat) : ℝ) := by
    have h := absTree_eq_natAbs hy
    exact_mod_cast (h ▸ habs)
  have hQ : ((kernelScaleMax : Nat) : ℝ) ≤ (2 : ℝ) ^ (127 : ℕ) := by
    unfold kernelScaleMax
    norm_num
  calc ((int256 y).natAbs : ℝ) * Real.exp z
      ≤ (2 : ℝ) ^ (127 : ℕ) * Real.exp z := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos z))
        linarith
    _ = Real.exp (z + 127 * Real.log 2) := hpow
    _ < 1 := hexp1

/-- **Clamp bracket.** The zero result satisfies the public bracket at or below the cutoff. -/
theorem mulExpRay_run_bracket_clamped {y x : Nat} (hy : Int128Word y) (hx : x < 2 ^ 256)
    (habs : absTree y ≤ kernelScaleMax) (hshift : 2 ≤ int256 (mulShiftTree y x))
    (hclamp : int256 x ≤ int256 mulExpRayZeroMax) :
    MulExpRayRunBracket y x := by
  refine ⟨0, run_mul_exp_ray_evm_clamped hy hx hshift hclamp, ?_⟩
  rw [int256_zero_word]
  have hlt := clamped_target_lt_one hy.1 hx habs hclamp
  have hnn := mulExpRayMagnitudeTarget_nonneg (int256 y) (int256 x)
  unfold MulExpRayBracket
  split_ifs <;>
    exact ⟨le_refl 0, by simpa using hnn, by push_cast; linarith⟩

end

end ExpYul
