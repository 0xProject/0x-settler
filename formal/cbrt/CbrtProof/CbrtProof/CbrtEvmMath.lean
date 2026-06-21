import FormalYul.Preservation
import CbrtProof.CbrtCorrect
import CbrtProof.CertifiedChain
import CbrtProof.FiniteCert
import CbrtProof.Wiring
import CbrtProof.OverflowSafety

set_option exponentiation.threshold 300

namespace CbrtEvmMath

open FormalYul
open CbrtCertified
open CbrtCert
open CbrtWiring

def cbrtUp256 (x : Nat) : Nat :=
  let z := innerCbrt x
  if z * z * z < x then z + 1 else z

private def cbrtCoreEvmBody (x : Nat) : Nat :=
  let b := evmSub 257 (evmClz x)
  let z := evmShr 7 (evmShl (evmDiv b 3)
    (evmAdd 90 (evmMul 26 (evmMod b 3))))
  let z := evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z z)) z) z) 3
  let z := evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z z)) z) z) 3
  let z := evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z z)) z) z) 3
  let z := evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z z)) z) z) 3
  evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z z)) z) z) 3

/- One normalized Newton step is the shared mathematical cbrt step. -/
private theorem normStep_eq_cbrtStep (x z : Nat) :
    normDiv (normAdd (normAdd (normDiv x (normMul z z)) z) z) 3 = cbrtStep x z := by
  simp [normDiv, normAdd, normMul, cbrtStep]
  omega

/-- The arithmetic seed expression decodes to the three cbrt seed multipliers. -/
private theorem seedExpr_eq (y : Nat) :
    normShr 7 (normShl (normDiv (y + 2) 3)
      (normAdd 90 (normMul 26 (normMod (y + 2) 3)))) =
      (cbrtSeedMultiplier y <<< (y / 3)) >>> 7 := by
  unfold normShr normShl normDiv normAdd normMul normMod cbrtSeedMultiplier
  have hcases : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by omega
  rcases hcases with h | h | h
  · have hmod : (y + 2) % 3 = 2 := by omega
    have hdiv : (y + 2) / 3 = y / 3 := by omega
    simp [h, hmod, hdiv, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  · have hmod : (y + 2) % 3 = 0 := by omega
    have hdiv : (y + 2) / 3 = y / 3 + 1 := by omega
    simp [h, hmod, hdiv, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.pow_succ]
    rw [Nat.mul_comm (2 ^ (y / 3)) 2, ← Nat.mul_assoc]
  · have hmod : (y + 2) % 3 = 1 := by omega
    have hdiv : (y + 2) / 3 = y / 3 + 1 := by omega
    simp [h, hmod, hdiv, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.pow_succ]
    rw [Nat.mul_comm (2 ^ (y / 3)) 2, ← Nat.mul_assoc]

private theorem cbrtSeedMultiplier_le_255 (y : Nat) :
    cbrtSeedMultiplier y ≤ 255 := by
  unfold cbrtSeedMultiplier
  have hmod_lt : y % 3 < 3 := Nat.mod_lt y (by decide)
  have hcases : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by omega
  rcases hcases with h | h | h <;> simp [h]

/-- For positive uint256 values, `257 - clz(x)` is exactly `log2(x) + 2`. -/
private theorem normSub257Clz_eq_log2_add_two_of_pos_u256
    (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    normSub 257 (normClz x) = Nat.log2 x + 2 := by
  unfold normSub normClz
  simp [Nat.ne_of_gt hx]
  have hlog : Nat.log2 x < 256 := (Nat.log2_lt (Nat.ne_of_gt hx)).2 hx256
  omega

/-- The direct normalized seed expression equals cbrtSeed for positive uint256 values. -/
private theorem normSub257Clz_eq_cbrtSeed_of_pos_u256
    (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    normShr 7 (normShl (normDiv (normSub 257 (normClz x)) 3)
      (normAdd 90 (normMul 26 (normMod (normSub 257 (normClz x)) 3)))) =
      cbrtSeed x := by
  have hy := normSub257Clz_eq_log2_add_two_of_pos_u256 x hx hx256
  rw [hy]
  rw [seedExpr_eq (Nat.log2 x)]
  rfl

private theorem innerCbrt_zero : innerCbrt 0 = 0 := by
  unfold innerCbrt cbrtSeed
  rw [Nat.log2_zero]
  decide

-- ============================================================================
-- Level 2: EVM helpers
-- ============================================================================

private theorem word_mod_gt_256 : 256 < WORD_MOD := by
  unfold WORD_MOD; decide

theorem u256_eq_of_lt (x : Nat) (hx : x < WORD_MOD) : u256 x = x := by
  unfold u256
  exact Nat.mod_eq_of_lt hx

private theorem evmClz_eq_normClz_of_u256 (x : Nat) (hx : x < WORD_MOD) :
    evmClz x = normClz x := by
  unfold evmClz normClz
  simp [u256_eq_of_lt x hx]

private theorem normClz_le_256 (x : Nat) : normClz x ≤ 256 := by
  unfold normClz; split <;> omega

private theorem evmSub_eq_normSub_of_le
    (a b : Nat) (ha : a < WORD_MOD) (hb : b ≤ a) :
    evmSub a b = normSub a b := by
  have hb' : b < WORD_MOD := Nat.lt_of_le_of_lt hb ha
  have hab' : a - b < WORD_MOD := Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
  unfold evmSub normSub
  simp [u256_eq_of_lt a ha, u256_eq_of_lt b hb']
  have hsplit : a + WORD_MOD - b = WORD_MOD + (a - b) := by omega
  unfold u256
  rw [hsplit, Nat.add_mod, Nat.mod_eq_zero_of_dvd (Nat.dvd_refl WORD_MOD), Nat.zero_add]
  simp [Nat.mod_eq_of_lt hab']

private theorem evmDiv_eq_normDiv_of_u256
    (x z : Nat) (hx : x < WORD_MOD) (hz : z < WORD_MOD) :
    evmDiv x z = normDiv x z := by
  by_cases hz0 : z = 0
  · subst hz0; unfold evmDiv normDiv u256; simp
  · unfold evmDiv normDiv
    rw [u256_eq_of_lt x hx, u256_eq_of_lt z hz]
    simp [hz0]

private theorem evmMod_eq_normMod_of_u256
    (x z : Nat) (hx : x < WORD_MOD) (hz : z < WORD_MOD) (hz0 : z ≠ 0) :
    evmMod x z = normMod x z := by
  unfold evmMod normMod
  rw [u256_eq_of_lt x hx, u256_eq_of_lt z hz]
  simp [hz0]

private theorem evmAdd_eq_normAdd_of_no_overflow
    (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) (hab : a + b < WORD_MOD) :
    evmAdd a b = normAdd a b := by
  unfold evmAdd normAdd
  simp [u256_eq_of_lt a ha, u256_eq_of_lt b hb, u256_eq_of_lt (a + b) hab]

private theorem evmOr_eq_normOr_of_u256
    (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmOr a b = normOr a b := by
  unfold evmOr normOr
  simp [u256_eq_of_lt a ha, u256_eq_of_lt b hb]

private theorem evmAnd_eq_normAnd_of_u256
    (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmAnd a b = normAnd a b := by
  unfold evmAnd normAnd
  simp [u256_eq_of_lt a ha, u256_eq_of_lt b hb]

private theorem evmByte_eq_normByte_of_u256
    (index value : Nat) (hindex : index < WORD_MOD) (hvalue : value < WORD_MOD) :
    evmByte index value = normByte index value := by
  unfold evmByte normByte
  simp [u256_eq_of_lt index hindex, u256_eq_of_lt value hvalue]

private theorem evmLt_eq_normLt_of_u256
    (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmLt a b = normLt a b := by
  unfold evmLt normLt; simp [u256_eq_of_lt a ha, u256_eq_of_lt b hb]

private theorem evmShr_eq_normShr_of_u256
    (s v : Nat) (hs : s < 256) (hv : v < WORD_MOD) :
    evmShr s v = normShr s v := by
  unfold evmShr normShr
  have hs' : s < WORD_MOD := Nat.lt_of_lt_of_le hs (Nat.le_of_lt word_mod_gt_256)
  simp [u256_eq_of_lt s hs', u256_eq_of_lt v hv, hs]

private theorem evmShl_eq_normShl_of_safe
    (s v : Nat) (hs : s < 256) (hv : v < WORD_MOD) (hvs : v * 2 ^ s < WORD_MOD) :
    evmShl s v = normShl s v := by
  unfold evmShl normShl
  have hs' : s < WORD_MOD := Nat.lt_of_lt_of_le hs (Nat.le_of_lt word_mod_gt_256)
  simp [u256_eq_of_lt s hs', u256_eq_of_lt v hv, hs, Nat.shiftLeft_eq]
  exact u256_eq_of_lt (v * 2 ^ s) hvs

private theorem evmMul_eq_normMul_of_no_overflow
    (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) (hab : a * b < WORD_MOD) :
    evmMul a b = normMul a b := by
  unfold evmMul normMul
  simp [u256_eq_of_lt a ha, u256_eq_of_lt b hb, u256_eq_of_lt (a * b) hab]

private theorem two_pow_lt_word (n : Nat) (hn : n < 256) :
    2 ^ n < WORD_MOD := by
  unfold WORD_MOD
  have hn_le : n ≤ 255 := by omega
  have hle : 2 ^ n ≤ 2 ^ 255 :=
    Nat.pow_le_pow_right (by decide : 1 ≤ (2 : Nat)) hn_le
  have hlt : 2 ^ 255 < 2 ^ 256 := by
    simp [Nat.pow_lt_pow_succ (a := 2) (n := 255) (by decide : 1 < (2 : Nat))]
  exact Nat.lt_of_le_of_lt hle hlt

private theorem one_lt_word : (1 : Nat) < WORD_MOD := by
  unfold WORD_MOD; decide

private theorem three_lt_word : (3 : Nat) < WORD_MOD := by
  unfold WORD_MOD; decide

private theorem two_fifty_five_lt_word : (255 : Nat) < WORD_MOD := by
  unfold WORD_MOD; decide

-- ============================================================================
-- Level 2: Key bounds for no-overflow
-- ============================================================================

-- m = icbrt(x) < 2^86 when x < 2^256
private theorem m_lt_pow86_of_u256
    (m x : Nat) (hmlo : m * m * m ≤ x) (hx : x < WORD_MOD) :
    m < 2 ^ 86 := by
  by_cases hm86 : m < 2 ^ 86
  · exact hm86
  · have hmGe : 2 ^ 86 ≤ m := Nat.le_of_not_lt hm86
    have h86sq : (2 ^ 86) * (2 ^ 86) ≤ m * m := Nat.mul_le_mul hmGe hmGe
    have h86cube : (2 ^ 86) * (2 ^ 86) * (2 ^ 86) ≤ m * m * m :=
      Nat.mul_le_mul h86sq hmGe
    have hpow_eq : (2 ^ 86) * (2 ^ 86) * (2 ^ 86) = 2 ^ 258 := by
      calc (2 ^ 86) * (2 ^ 86) * (2 ^ 86)
          = 2 ^ (86 + 86) * (2 ^ 86) := by rw [← Nat.pow_add]
        _ = 2 ^ (86 + 86 + 86) := by rw [← Nat.pow_add]
        _ = 2 ^ 258 := by decide
    have hxGe : 2 ^ 258 ≤ x := by omega
    have hword : WORD_MOD ≤ 2 ^ 258 := by
      unfold WORD_MOD
      exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by decide : 256 ≤ 258)
    exact False.elim ((Nat.not_lt_of_ge (Nat.le_trans hword hxGe)) hx)

-- Overflow bound: x/(z*z) + 2*z < WORD_MOD when z ≤ 2m and m < 2^86
private theorem cbrt_sum_lt_word_of_bounds
    (x m z : Nat)
    (hx : x < WORD_MOD)
    (hm : 0 < m)
    (hmlo : m * m * m ≤ x)
    (hmhi : x < (m + 1) * (m + 1) * (m + 1))
    (hmz : m ≤ z)
    (hz2m : z ≤ 2 * m) :
    x / (z * z) + 2 * z < WORD_MOD := by
  have hm86 : m < 2 ^ 86 := m_lt_pow86_of_u256 m x hmlo hx
  have hmm : 0 < m * m := Nat.mul_pos hm hm
  -- x/(z*z) ≤ x/(m*m)
  have hdiv_mono : x / (z * z) ≤ x / (m * m) :=
    Nat.div_le_div_left (Nat.mul_le_mul hmz hmz) hmm
  -- x ≤ m^3 + 3m^2 + 3m (from x < (m+1)^3)
  have hxle : x ≤ m * m * m + 3 * (m * m) + 3 * m := by
    have : (m + 1) * (m + 1) * (m + 1) = m * m * m + 3 * (m * m) + 3 * m + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.mul_assoc, Nat.add_assoc]
      omega
    omega
  have hdiv_bound : x / (m * m) ≤ m + 6 := by
    -- m^3 + 3m^2 + 3m ≤ (m*m) * (m + 6) since:
    -- (m*m) * (m+6) = m^3 + 6m^2 ≥ m^3 + 3m^2 + 3m (when 3m^2 ≥ 3m, i.e., m ≥ 1)
    have h1 : m * m * m + 3 * (m * m) + 3 * m ≤ (m * m) * (m + 6) := by
      -- (m*m)*(m+6) = m*m*m + 6*(m*m)
      have hexpand : (m * m) * (m + 6) = m * m * m + 6 * (m * m) := by
        rw [Nat.mul_add, Nat.mul_comm (m * m) 6]
      rw [hexpand]
      -- Need: 3*(m*m) + 3*m ≤ 6*(m*m), i.e., 3*m ≤ 3*(m*m), i.e., m ≤ m*m
      have hmm_ge : m ≤ m * m := by
        calc m = m * 1 := by omega
          _ ≤ m * m := Nat.mul_le_mul_left m (Nat.succ_le_of_lt hm)
      omega
    exact Nat.le_trans (Nat.div_le_div_right hxle) (Nat.div_le_of_le_mul h1)
  have hdiv : x / (z * z) ≤ m + 6 := Nat.le_trans hdiv_mono hdiv_bound
  have hbound : 5 * (2 ^ 86) + 6 < WORD_MOD := by unfold WORD_MOD; decide
  omega

-- z * z < WORD_MOD when z < 2^87
private theorem zsq_lt_word_of_lt_87 (z : Nat) (hz : z < 2 ^ 87) :
    z * z < WORD_MOD := by
  by_cases hz0 : z = 0
  · subst hz0; unfold WORD_MOD; decide
  · have hzPos : 0 < z := Nat.pos_of_ne_zero hz0
    -- z * z < 2^87 * z (from z < 2^87 and z > 0)
    have h1 : z * z < 2 ^ 87 * z := Nat.mul_lt_mul_of_pos_right hz hzPos
    -- 2^87 * z < 2^87 * 2^87 (from z < 2^87 and 2^87 > 0)
    have h2 : 2 ^ 87 * z < 2 ^ 87 * 2 ^ 87 :=
      Nat.mul_lt_mul_of_pos_left hz (Nat.two_pow_pos 87)
    have hpow : 2 ^ 87 * 2 ^ 87 = 2 ^ 174 := by rw [← Nat.pow_add]
    have h174 : 2 ^ 174 < WORD_MOD := two_pow_lt_word 174 (by decide)
    omega

-- One cbrt step: EVM = Nat when no overflow
private theorem step_evm_eq_norm_of_safe
    (x z : Nat)
    (hx : x < WORD_MOD)
    (_hzPos : 0 < z)
    (hz : z < WORD_MOD)
    (hzzW : z * z < WORD_MOD)
    (hsum : x / (z * z) + 2 * z < WORD_MOD) :
    evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z z)) z) z) 3 =
      normDiv (normAdd (normAdd (normDiv x (normMul z z)) z) z) 3 := by
  -- evmMul z z = normMul z z
  have hmul : evmMul z z = normMul z z :=
    evmMul_eq_normMul_of_no_overflow z z hz hz hzzW
  have hmulLt : normMul z z < WORD_MOD := by simpa [normMul] using hzzW
  -- evmDiv x (evmMul z z) = normDiv x (normMul z z)
  have hdiv1 : evmDiv x (evmMul z z) = normDiv x (normMul z z) := by
    rw [hmul]; exact evmDiv_eq_normDiv_of_u256 x (normMul z z) hx hmulLt
  have hdivVal : normDiv x (normMul z z) = x / (z * z) := by simp [normDiv, normMul]
  have hdivLt : normDiv x (normMul z z) < WORD_MOD := by
    rw [hdivVal]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  -- First add: (x/(z*z)) + z
  have haddLt1 : x / (z * z) + z < WORD_MOD := by
    have : x / (z * z) + z ≤ x / (z * z) + 2 * z := by omega
    exact Nat.lt_of_le_of_lt this hsum
  have hadd1 : evmAdd (evmDiv x (evmMul z z)) z = normAdd (normDiv x (normMul z z)) z := by
    rw [hdiv1]
    exact evmAdd_eq_normAdd_of_no_overflow (normDiv x (normMul z z)) z hdivLt hz
      (by simpa [normAdd, hdivVal] using haddLt1)
  -- Second add: (x/(z*z) + z) + z
  have hadd1Val : normAdd (normDiv x (normMul z z)) z = x / (z * z) + z := by
    simp [normAdd, hdivVal]
  have hadd1Lt : normAdd (normDiv x (normMul z z)) z < WORD_MOD := by
    rw [hadd1Val]; exact haddLt1
  have hsum2 : normAdd (normDiv x (normMul z z)) z + z < WORD_MOD := by
    rw [hadd1Val]; have : x / (z * z) + z + z = x / (z * z) + 2 * z := by omega
    omega
  have hadd2 : evmAdd (evmAdd (evmDiv x (evmMul z z)) z) z =
      normAdd (normAdd (normDiv x (normMul z z)) z) z := by
    rw [hadd1]
    exact evmAdd_eq_normAdd_of_no_overflow
      (normAdd (normDiv x (normMul z z)) z) z hadd1Lt hz
      (by simpa [normAdd] using hsum2)
  -- Division by 3
  have hsumLt : normAdd (normAdd (normDiv x (normMul z z)) z) z < WORD_MOD := by
    simp [normAdd, hdivVal]
    have : x / (z * z) + z + z = x / (z * z) + 2 * z := by omega
    omega
  rw [hadd2]
  exact evmDiv_eq_normDiv_of_u256
    (normAdd (normAdd (normDiv x (normMul z z)) z) z) 3 hsumLt three_lt_word

private theorem normLt_div_zsq_le (x z : Nat) :
    normLt (normDiv x (normMul z z)) z ≤ z := by
  by_cases hz0 : z = 0
  · subst hz0
    simp [normLt, normDiv, normMul]
  · by_cases hlt : x / (z * z) < z
    · simp [normLt, normDiv, normMul, hlt]
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hz0)
    · simp [normLt, normDiv, normMul, hlt]

private theorem floor_step_evm_eq_norm
    (x z : Nat) (hx : x < WORD_MOD) (hz : z < WORD_MOD) (hzzW : z * z < WORD_MOD) :
    evmSub z (evmLt (evmDiv x (evmMul z z)) z) =
      normSub z (normLt (normDiv x (normMul z z)) z) := by
  have hmul : evmMul z z = normMul z z :=
    evmMul_eq_normMul_of_no_overflow z z hz hz hzzW
  have hmulLt : normMul z z < WORD_MOD := by simpa [normMul] using hzzW
  have hdiv : evmDiv x (evmMul z z) = normDiv x (normMul z z) := by
    rw [hmul]
    exact evmDiv_eq_normDiv_of_u256 x (normMul z z) hx hmulLt
  have hdivLt : normDiv x (normMul z z) < WORD_MOD :=
    Nat.lt_of_le_of_lt (by simp [normDiv, normMul]; exact Nat.div_le_self _ _) hx
  have hlt : evmLt (evmDiv x (evmMul z z)) z =
      normLt (normDiv x (normMul z z)) z := by
    simpa [hdiv] using evmLt_eq_normLt_of_u256 (normDiv x (normMul z z)) z hdivLt hz
  have hbLe : normLt (normDiv x (normMul z z)) z ≤ z := normLt_div_zsq_le x z
  calc evmSub z (evmLt (evmDiv x (evmMul z z)) z)
      = evmSub z (normLt (normDiv x (normMul z z)) z) := by rw [hlt]
    _ = normSub z (normLt (normDiv x (normMul z z)) z) :=
        evmSub_eq_normSub_of_le z (normLt (normDiv x (normMul z z)) z) hz hbLe

private theorem floor_correction_norm_eq_if (x z : Nat) :
    normSub z (normLt (normDiv x (normMul z z)) z) =
      (if x / (z * z) < z then z - 1 else z) := by
  by_cases hz0 : z = 0
  · subst hz0
    simp [normSub, normLt, normDiv, normMul]
  · by_cases hlt : x / (z * z) < z
    · simp [normSub, normLt, normDiv, normMul, hlt]
    · simp [normSub, normLt, normDiv, normMul, hlt]

-- Seed: EVM = Nat
private theorem seed_evm_eq_norm (x : Nat) (hxPos : 0 < x) (hxWord : x < WORD_MOD) :
    evmShr 7 (evmShl (evmDiv (evmSub 257 (evmClz x)) 3)
      (evmAdd 90 (evmMul 26 (evmMod (evmSub 257 (evmClz x)) 3)))) =
      normShr 7 (normShl (normDiv (normSub 257 (normClz x)) 3)
        (normAdd 90 (normMul 26 (normMod (normSub 257 (normClz x)) 3)))) := by
  have hclz : evmClz x = normClz x := evmClz_eq_normClz_of_u256 x hxWord
  have h257W : (257 : Nat) < WORD_MOD := by unfold WORD_MOD; decide
  have hclzLe257 : normClz x ≤ 257 := by
    unfold normClz
    simp [Nat.ne_of_gt hxPos]
    omega
  have hsub : evmSub 257 (evmClz x) = normSub 257 (normClz x) := by
    simpa [hclz] using evmSub_eq_normSub_of_le 257 (normClz x) h257W hclzLe257
  let b := normSub 257 (normClz x)
  have hbLe : b ≤ 257 := by dsimp [b]; unfold normSub; exact Nat.sub_le _ _
  have hbLt : b < WORD_MOD := Nat.lt_of_le_of_lt hbLe h257W
  let r := normMod b 3
  let multiplier := normAdd 90 (normMul 26 r)
  let q := normDiv b 3
  -- evmDiv (...) 3 = normDiv (...) 3
  have hdiv : evmDiv (evmSub 257 (evmClz x)) 3 = q := by
    rw [hsub]
    dsimp [q, b]
    exact evmDiv_eq_normDiv_of_u256 (normSub 257 (normClz x)) 3 hbLt three_lt_word
  -- evmMod (...) 3 = normMod (...) 3
  have hmod : evmMod (evmSub 257 (evmClz x)) 3 = r := by
    rw [hsub]
    dsimp [r, b]
    exact evmMod_eq_normMod_of_u256 (normSub 257 (normClz x)) 3 hbLt three_lt_word (by decide)
  have hrLe : r ≤ 2 := by
    dsimp [r]
    unfold normMod
    have := Nat.mod_lt b (by decide : 0 < 3)
    omega
  have hrLtW : r < WORD_MOD := by omega
  have hmulLt : normMul 26 r < WORD_MOD := by
    unfold normMul
    have h52 : 26 * r ≤ 52 := by omega
    have h52W : (52 : Nat) < WORD_MOD := by unfold WORD_MOD; decide
    exact Nat.lt_of_le_of_lt h52 h52W
  have hmul : evmMul 26 (evmMod (evmSub 257 (evmClz x)) 3) = normMul 26 r := by
    rw [hmod]
    exact evmMul_eq_normMul_of_no_overflow 26 r
      (by unfold WORD_MOD; decide) hrLtW hmulLt
  have hmult : evmAdd 90 (evmMul 26 (evmMod (evmSub 257 (evmClz x)) 3)) =
      multiplier := by
    rw [hmul]
    dsimp [multiplier]
    exact evmAdd_eq_normAdd_of_no_overflow 90 (normMul 26 r)
      (by unfold WORD_MOD; decide) hmulLt (by
        have h142 : 90 + normMul 26 r ≤ 142 := by
          unfold normMul
          omega
        have h142W : (142 : Nat) < WORD_MOD := by unfold WORD_MOD; decide
        exact Nat.lt_of_le_of_lt h142 h142W)
  have hmultLe : multiplier ≤ 142 := by
    dsimp [multiplier]
    unfold normAdd normMul
    omega
  have hmultW : multiplier < WORD_MOD := by
    have h142W : (142 : Nat) < WORD_MOD := by unfold WORD_MOD; decide
    exact Nat.lt_of_le_of_lt hmultLe h142W
  -- q := normDiv result ≤ 85
  have hdivLe : q ≤ 85 := by
    dsimp [q]
    unfold normDiv
    exact Nat.le_trans (Nat.div_le_div_right hbLe) (by decide)
  have hdivLt256 : q < 256 := by omega
  have hqLt : q < 256 := hdivLt256
  have hshlSafe : multiplier * 2 ^ q < WORD_MOD := by
    have h1 : multiplier * 2 ^ q ≤ 142 * 2 ^ 85 :=
      Nat.mul_le_mul hmultLe (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hdivLe)
    have h2 : 142 * 2 ^ 85 < 2 ^ 93 := by decide
    have h3 : 2 ^ 93 < WORD_MOD := two_pow_lt_word 93 (by decide)
    omega
  have hshl : evmShl (evmDiv (evmSub 257 (evmClz x)) 3)
      (evmAdd 90 (evmMul 26 (evmMod (evmSub 257 (evmClz x)) 3))) =
      normShl q multiplier := by
    rw [hdiv, hmult]
    exact evmShl_eq_normShl_of_safe q multiplier hqLt hmultW hshlSafe
  have hshlVal : normShl q multiplier < WORD_MOD := by
    unfold normShl
    rw [Nat.shiftLeft_eq]
    exact hshlSafe
  have hshr : evmShr 7 (evmShl (evmDiv (evmSub 257 (evmClz x)) 3)
      (evmAdd 90 (evmMul 26 (evmMod (evmSub 257 (evmClz x)) 3)))) =
      normShr 7 (normShl q multiplier) := by
    rw [hshl]
    exact evmShr_eq_normShr_of_u256 7 (normShl q multiplier) (by decide) hshlVal
  rw [hshr]

-- ============================================================================
-- Level 2: Interpreted core arithmetic
-- ============================================================================

set_option maxRecDepth 1000000 in
-- Seed squared fits in uint256 for every certificate octave.
private theorem seed_sq_lt_word : ∀ i : Fin 248,
    seedOf i * seedOf i < WORD_MOD := by decide

-- The seed NR step numerator fits in uint256 for every certificate octave.
-- For octave i (bit-length i+8), x < 2^(i+9), so:
--   x/(seed²) + 2*seed ≤ (2^(i+9)-1)/(seed²) + 2*seed < WORD_MOD
set_option maxRecDepth 1000000 in
private theorem seed_sum_lt_word : ∀ i : Fin 248,
    (2 ^ (i.val + certOffset + 1) - 1) / (seedOf i * seedOf i) + 2 * seedOf i < WORD_MOD := by
  decide

private theorem cbrtSeed_small_pos_le_255
    (x : Nat) (hx : 0 < x) (hxSmall : x < 256) :
    0 < cbrtSeed x ∧ cbrtSeed x ≤ 255 := by
  have hlog : Nat.log2 x < 8 :=
    (Nat.log2_lt (Nat.ne_of_gt hx)).2 (by simpa using hxSmall)
  have hcases : Nat.log2 x = 0 ∨ Nat.log2 x = 1 ∨ Nat.log2 x = 2 ∨
      Nat.log2 x = 3 ∨ Nat.log2 x = 4 ∨ Nat.log2 x = 5 ∨
      Nat.log2 x = 6 ∨ Nat.log2 x = 7 := by
    omega
  rcases hcases with h | h | h | h | h | h | h | h <;>
    simp [cbrtSeed, cbrtSeedMultiplier, h, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow]

private theorem cbrtStep_small_pos_le_255
    (x z : Nat) (hx : 0 < x) (hxSmall : x < 256)
    (hzPos : 0 < z) (hzLe : z ≤ 255) :
    0 < cbrtStep x z ∧ cbrtStep x z ≤ 255 := by
  unfold cbrtStep
  have hxLe : x ≤ 255 := by omega
  have hdivLe : x / (z * z) ≤ x := Nat.div_le_self x (z * z)
  have hsumLe : x / (z * z) + 2 * z ≤ 765 := by
    have h2z : 2 * z ≤ 510 := Nat.mul_le_mul_left 2 hzLe
    omega
  constructor
  · have hnum : 3 ≤ x / (z * z) + 2 * z := by
      by_cases hz1 : z = 1
      · subst hz1
        simp
        omega
      · have hz2 : 2 ≤ z := by omega
        have h2z : 3 ≤ 2 * z := by omega
        have hdivNonneg : 0 ≤ x / (z * z) := Nat.zero_le _
        omega
    exact Nat.div_pos hnum (by decide : 0 < 3)
  · exact Nat.le_trans (Nat.div_le_div_right hsumLe) (by decide)

private theorem cbrt_step_small_evm_eq
    (x z : Nat) (hxWord : x < WORD_MOD) (hxSmall : x < 256)
    (hzPos : 0 < z) (hzLe : z ≤ 255) :
    evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z z)) z) z) 3 = cbrtStep x z := by
  have hzW : z < WORD_MOD :=
    Nat.lt_of_le_of_lt hzLe two_fifty_five_lt_word
  have hzzW : z * z < WORD_MOD := by
    have hzz : z * z ≤ 255 * 255 := Nat.mul_le_mul hzLe hzLe
    exact Nat.lt_of_le_of_lt hzz (by unfold WORD_MOD; decide)
  have hsum : x / (z * z) + 2 * z < WORD_MOD := by
    have hxLe : x ≤ 255 := by omega
    have hdivLe : x / (z * z) ≤ x := Nat.div_le_self x (z * z)
    have h2z : 2 * z ≤ 510 := Nat.mul_le_mul_left 2 hzLe
    exact Nat.lt_of_le_of_lt (by omega : x / (z * z) + 2 * z ≤ 765)
      (by unfold WORD_MOD; decide)
  have h := step_evm_eq_norm_of_safe x z hxWord hzPos hzW hzzW hsum
  simpa [normStep_eq_cbrtStep] using h

private theorem cbrtCoreEvmBody_eq_innerCbrt_small
    (x : Nat) (hx : 0 < x) (hxSmall : x < 256) :
    cbrtCoreEvmBody x = innerCbrt x := by
  have hxWord : x < WORD_MOD :=
    Nat.lt_trans hxSmall word_mod_gt_256
  have hseedEvm :
      evmShr 7 (evmShl (evmDiv (evmSub 257 (evmClz x)) 3)
        (evmAdd 90 (evmMul 26 (evmMod (evmSub 257 (evmClz x)) 3)))) =
        cbrtSeed x := by
    exact (seed_evm_eq_norm x hx hxWord).trans
      (normSub257Clz_eq_cbrtSeed_of_pos_u256 x hx (by simpa [WORD_MOD] using hxWord))
  let z0 := cbrtSeed x
  let z1 := cbrtStep x z0
  let z2 := cbrtStep x z1
  let z3 := cbrtStep x z2
  let z4 := cbrtStep x z3
  let z5 := cbrtStep x z4
  have hz0 : 0 < z0 ∧ z0 ≤ 255 := by
    simpa [z0] using cbrtSeed_small_pos_le_255 x hx hxSmall
  have hz1 : 0 < z1 ∧ z1 ≤ 255 := by
    simpa [z0, z1] using cbrtStep_small_pos_le_255 x z0 hx hxSmall hz0.1 hz0.2
  have hz2 : 0 < z2 ∧ z2 ≤ 255 := by
    simpa [z1, z2] using cbrtStep_small_pos_le_255 x z1 hx hxSmall hz1.1 hz1.2
  have hz3 : 0 < z3 ∧ z3 ≤ 255 := by
    simpa [z2, z3] using cbrtStep_small_pos_le_255 x z2 hx hxSmall hz2.1 hz2.2
  have hz4 : 0 < z4 ∧ z4 ≤ 255 := by
    simpa [z3, z4] using cbrtStep_small_pos_le_255 x z3 hx hxSmall hz3.1 hz3.2
  have hstep1 : evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z0 z0)) z0) z0) 3 = z1 := by
    simpa [z1] using cbrt_step_small_evm_eq x z0 hxWord hxSmall hz0.1 hz0.2
  have hstep2 : evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z1 z1)) z1) z1) 3 = z2 := by
    simpa [z2] using cbrt_step_small_evm_eq x z1 hxWord hxSmall hz1.1 hz1.2
  have hstep3 : evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z2 z2)) z2) z2) 3 = z3 := by
    simpa [z3] using cbrt_step_small_evm_eq x z2 hxWord hxSmall hz2.1 hz2.2
  have hstep4 : evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z3 z3)) z3) z3) 3 = z4 := by
    simpa [z4] using cbrt_step_small_evm_eq x z3 hxWord hxSmall hz3.1 hz3.2
  have hstep5 : evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z4 z4)) z4) z4) 3 = z5 := by
    simpa [z5] using cbrt_step_small_evm_eq x z4 hxWord hxSmall hz4.1 hz4.2
  unfold cbrtCoreEvmBody innerCbrt
  simp [hseedEvm, z0, z1, z2, z3, z4, z5,
    hstep1, hstep2, hstep3, hstep4, hstep5]

private theorem cbrtCoreEvmBody_eq_innerCbrt_of_steps
    (x z0 z1 z2 z3 z4 z5 : Nat)
    (hseedEvm :
      evmShr 7 (evmShl (evmDiv (evmSub 257 (evmClz x)) 3)
        (evmAdd 90 (evmMul 26 (evmMod (evmSub 257 (evmClz x)) 3)))) = z0)
    (hseedNat : cbrtSeed x = z0)
    (hstep1 : evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z0 z0)) z0) z0) 3 = z1)
    (hstep2 : evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z1 z1)) z1) z1) 3 = z2)
    (hstep3 : evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z2 z2)) z2) z2) 3 = z3)
    (hstep4 : evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z3 z3)) z3) z3) 3 = z4)
    (hstep5 : evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z4 z4)) z4) z4) 3 = z5)
    (hnat1 : cbrtStep x z0 = z1)
    (hnat2 : cbrtStep x z1 = z2)
    (hnat3 : cbrtStep x z2 = z3)
    (hnat4 : cbrtStep x z3 = z4)
    (hnat5 : cbrtStep x z4 = z5) :
    cbrtCoreEvmBody x = innerCbrt x := by
  unfold cbrtCoreEvmBody innerCbrt
  simp [hseedEvm, hseedNat, hstep1, hstep2, hstep3, hstep4, hstep5,
    hnat1, hnat2, hnat3, hnat4, hnat5]

private theorem cbrtCoreEvmBody_eq_innerCbrt_large
    (x : Nat)
    (hx256 : x < WORD_MOD)
    (hx : 0 < x)
    (hx_small : ¬ x < 256) :
    cbrtCoreEvmBody x = innerCbrt x := by
  have hx256_le : 256 ≤ x := Nat.le_of_not_lt hx_small
  let m := icbrt x
  have hmlo : m * m * m ≤ x := icbrt_cube_le x
  have hmhi : x < (m + 1) * (m + 1) * (m + 1) := icbrt_lt_succ_cube x
  have hm86 : m < 2 ^ 86 := m_lt_pow86_of_u256 m x hmlo hx256
  -- m ≥ 6 since x ≥ 256 and 6³ = 216 ≤ 256
  have hm6 : 6 ≤ m := by
    by_cases hm6 : 6 ≤ m
    · exact hm6
    · have hlt : m < 6 := Nat.lt_of_not_ge hm6
      have h6cube : (m + 1) * (m + 1) * (m + 1) ≤ 6 * 6 * 6 :=
        cube_monotone (by omega : m + 1 ≤ 6)
      have : x < 216 := Nat.lt_of_lt_of_le hmhi h6cube
      omega
  have hm : 0 < m := by omega
  -- Map to certificate octave
  let n := Nat.log2 x
  have hn8 : 8 ≤ n := by
    dsimp [n]
    by_cases h8 : 8 ≤ Nat.log2 x
    · exact h8
    · have hlog := (CbrtCompat.log2_eq_iff (Nat.ne_of_gt hx)).1 rfl
      have hlt : Nat.log2 x + 1 ≤ 8 := by omega
      have hpow : 2 ^ (Nat.log2 x + 1) ≤ 2 ^ 8 :=
        Nat.pow_le_pow_right (by decide : 1 ≤ 2) hlt
      have : x < 256 := Nat.lt_of_lt_of_le hlog.2 (by simpa using hpow)
      omega
  have hn_lt : n < 256 := (Nat.log2_lt (Nat.ne_of_gt hx)).2 hx256
  have hn_sub_lt : n - certOffset < 248 := by dsimp [n, certOffset]; omega
  let idx : Fin 248 := ⟨n - certOffset, hn_sub_lt⟩
  have hidx_plus : idx.val + certOffset = n := by dsimp [idx, certOffset, n]; omega
  have hOct : 2 ^ (idx.val + certOffset) ≤ x ∧ x < 2 ^ (idx.val + certOffset + 1) := by
    rw [hidx_plus]
    exact (CbrtCompat.log2_eq_iff (Nat.ne_of_gt hx)).1 rfl
  -- Seed and interval
  have hseedOf : cbrtSeed x = seedOf idx := CbrtWiring.cbrtSeed_eq_certSeed idx x hOct
  have hinterval := CbrtWiring.m_within_cert_interval idx x m hmlo hmhi hOct
  -- Define z0..z5
  let z0 := seedOf idx
  let z1 := cbrtStep x z0
  let z2 := cbrtStep x z1
  let z3 := cbrtStep x z2
  let z4 := cbrtStep x z3
  let z5 := cbrtStep x z4
  have hsPos : 0 < z0 := seed_pos idx
  have hm2 : 2 ≤ m := Nat.le_trans (lo_ge_two idx) hinterval.1
  have hstepBounds := CbrtCertified.run4_certified_step_bounds idx x m
    hm2 hmlo hmhi hinterval.1 hinterval.2
  dsimp only at hstepBounds
  rcases hstepBounds with
    ⟨hmz1, hd1, h2d1, hmz2, hd2, h2d2,
      hmz3, hd3, h2d3, hmz4, hd4, h2d4⟩
  have hmz1L : m ≤ z1 := by simpa [z0, z1] using hmz1
  have hd1L : z1 - m ≤ d1Of idx := by simpa [z0, z1] using hd1
  have hmz2L : m ≤ z2 := by simpa [z0, z1, z2] using hmz2
  have hd2L : z2 - m ≤ d2Of idx := by simpa [z0, z1, z2] using hd2
  have hmz3L : m ≤ z3 := by simpa [z0, z1, z2, z3] using hmz3
  have hd3L : z3 - m ≤ d3Of idx := by simpa [z0, z1, z2, z3] using hd3
  have hmz4L : m ≤ z4 := by simpa [z0, z1, z2, z3, z4] using hmz4
  have hd4L : z4 - m ≤ d4Of idx := by simpa [z0, z1, z2, z3, z4] using hd4
  have hz1Pos : 0 < z1 := Nat.lt_of_lt_of_le hm hmz1L
  have hz2Pos : 0 < z2 := Nat.lt_of_lt_of_le hm hmz2L
  have hz3Pos : 0 < z3 := Nat.lt_of_lt_of_le hm hmz3L
  have hz4Pos : 0 < z4 := Nat.lt_of_lt_of_le hm hmz4L
  -- Upper bounds: z_k ≤ 2m (from error ≤ d_k ≤ lo/2 ≤ m/2, so z_k ≤ m + m/2 < 2m)
  -- Actually: 2*d_k ≤ lo ≤ m, so d_k ≤ m/2, so z_k ≤ m + d_k ≤ m + m = 2m
  have hd1m : d1Of idx ≤ m := by omega
  have hd2m : d2Of idx ≤ m := by omega
  have hd3m : d3Of idx ≤ m := by omega
  have hd4m : d4Of idx ≤ m := by omega
  have hz1_le_2m : z1 ≤ 2 * m := by omega
  have hz2_le_2m : z2 ≤ 2 * m := by omega
  have hz3_le_2m : z3 ≤ 2 * m := by omega
  have hz4_le_2m : z4 ≤ 2 * m := by omega
  -- z_k < 2^87 (from z_k ≤ 2m < 2^87)
  have hz1_87 : z1 < 2 ^ 87 := by omega
  have hz2_87 : z2 < 2 ^ 87 := by omega
  have hz3_87 : z3 < 2 ^ 87 := by omega
  have hz4_87 : z4 < 2 ^ 87 := by omega
  -- z_k * z_k < WORD_MOD (from z_k < 2^87)
  have hzz1 : z1 * z1 < WORD_MOD := zsq_lt_word_of_lt_87 z1 hz1_87
  have hzz2 : z2 * z2 < WORD_MOD := zsq_lt_word_of_lt_87 z2 hz2_87
  have hzz3 : z3 * z3 < WORD_MOD := zsq_lt_word_of_lt_87 z3 hz3_87
  have hzz4 : z4 * z4 < WORD_MOD := zsq_lt_word_of_lt_87 z4 hz4_87
  -- x/(z_k*z_k) + 2*z_k < WORD_MOD (from cbrt_sum_lt_word_of_bounds)
  have hsum1 : x / (z1 * z1) + 2 * z1 < WORD_MOD :=
    cbrt_sum_lt_word_of_bounds x m z1 hx256 hm hmlo hmhi hmz1L hz1_le_2m
  have hsum2 : x / (z2 * z2) + 2 * z2 < WORD_MOD :=
    cbrt_sum_lt_word_of_bounds x m z2 hx256 hm hmlo hmhi hmz2L hz2_le_2m
  have hsum3 : x / (z3 * z3) + 2 * z3 < WORD_MOD :=
    cbrt_sum_lt_word_of_bounds x m z3 hx256 hm hmlo hmhi hmz3L hz3_le_2m
  have hsum4 : x / (z4 * z4) + 2 * z4 < WORD_MOD :=
    cbrt_sum_lt_word_of_bounds x m z4 hx256 hm hmlo hmhi hmz4L hz4_le_2m
  -- Seed step: z0*z0 < WORD_MOD and x/(z0*z0) + 2*z0 < WORD_MOD
  have hzz0 : z0 * z0 < WORD_MOD := seed_sq_lt_word idx
  have hsum0 : x / (z0 * z0) + 2 * z0 < WORD_MOD := by
    have hseed_bound := seed_sum_lt_word idx
    have hxup : x < 2 ^ (idx.val + certOffset + 1) := hOct.2
    have hx_div_le : x / (seedOf idx * seedOf idx) ≤
        (2 ^ (idx.val + certOffset + 1) - 1) / (seedOf idx * seedOf idx) := by
      exact Nat.div_le_div_right (by omega)
    calc x / (z0 * z0) + 2 * z0
        ≤ (2 ^ (idx.val + certOffset + 1) - 1) / (seedOf idx * seedOf idx) + 2 * seedOf idx :=
          Nat.add_le_add_right hx_div_le _
      _ < WORD_MOD := hseed_bound
  -- z_k < WORD_MOD
  have hz0W : z0 < WORD_MOD := by
    have hle : z0 ≤ z0 * z0 := by
      calc z0 = z0 * 1 := by omega
        _ ≤ z0 * z0 := Nat.mul_le_mul_left z0 (Nat.succ_le_of_lt hsPos)
    exact Nat.lt_of_le_of_lt hle hzz0
  have hz1W : z1 < WORD_MOD := Nat.lt_of_lt_of_le hz1_87 (Nat.le_of_lt (two_pow_lt_word 87 (by decide)))
  have hz2W : z2 < WORD_MOD := Nat.lt_of_lt_of_le hz2_87 (Nat.le_of_lt (two_pow_lt_word 87 (by decide)))
  have hz3W : z3 < WORD_MOD := Nat.lt_of_lt_of_le hz3_87 (Nat.le_of_lt (two_pow_lt_word 87 (by decide)))
  have hz4W : z4 < WORD_MOD := Nat.lt_of_lt_of_le hz4_87 (Nat.le_of_lt (two_pow_lt_word 87 (by decide)))
  -- EVM step = norm step for each iteration
  have hstep1 : evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z0 z0)) z0) z0) 3 = z1 := by
    have h := step_evm_eq_norm_of_safe x z0 hx256 hsPos hz0W hzz0 hsum0
    simpa [z1, normStep_eq_cbrtStep] using h
  have hstep2 : evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z1 z1)) z1) z1) 3 = z2 := by
    have h := step_evm_eq_norm_of_safe x z1 hx256 hz1Pos hz1W hzz1 hsum1
    simpa [z2, normStep_eq_cbrtStep] using h
  have hstep3 : evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z2 z2)) z2) z2) 3 = z3 := by
    have h := step_evm_eq_norm_of_safe x z2 hx256 hz2Pos hz2W hzz2 hsum2
    simpa [z3, normStep_eq_cbrtStep] using h
  have hstep4 : evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z3 z3)) z3) z3) 3 = z4 := by
    have h := step_evm_eq_norm_of_safe x z3 hx256 hz3Pos hz3W hzz3 hsum3
    simpa [z4, normStep_eq_cbrtStep] using h
  have hstep5 : evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z4 z4)) z4) z4) 3 = z5 := by
    have h := step_evm_eq_norm_of_safe x z4 hx256 hz4Pos hz4W hzz4 hsum4
    simpa [z5, normStep_eq_cbrtStep] using h
  -- Seed: EVM = norm
  have hseedEvm :
      evmShr 7 (evmShl (evmDiv (evmSub 257 (evmClz x)) 3)
        (evmAdd 90 (evmMul 26 (evmMod (evmSub 257 (evmClz x)) 3)))) =
        seedOf idx := by
    have hseedNorm' := (normSub257Clz_eq_cbrtSeed_of_pos_u256 x hx hx256).trans hseedOf
    exact (seed_evm_eq_norm x hx hx256).trans hseedNorm'
  -- Final assembly
  exact cbrtCoreEvmBody_eq_innerCbrt_of_steps x z0 z1 z2 z3 z4 z5
    hseedEvm hseedOf hstep1 hstep2 hstep3 hstep4 hstep5
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)

private theorem cbrtCoreEvmBody_eq_innerCbrt_zero :
    cbrtCoreEvmBody 0 = innerCbrt 0 := by
  simp [cbrtCoreEvmBody, innerCbrt_zero, evmSub, evmClz,
    evmShr, evmShl, evmDiv, evmAdd, evmMul, evmMod, u256, WORD_MOD]

private theorem cbrtCoreEvmBody_eq_innerCbrt_pos
    (x : Nat)
    (hx256 : x < WORD_MOD)
    (hx : 0 < x) :
    cbrtCoreEvmBody x = innerCbrt x := by
  by_cases hx_small : x < 256
  · exact cbrtCoreEvmBody_eq_innerCbrt_small x hx hx_small
  · exact cbrtCoreEvmBody_eq_innerCbrt_large x hx256 hx hx_small

theorem cbrtCoreEvmExpression_eq_innerCbrt (x : Nat) :
    (let x := u256 x
     let b := evmSub 257 (evmClz x)
     let z := evmShr 7 (evmShl (evmDiv b 3)
       (evmAdd 90 (evmMul 26 (evmMod b 3))))
     let z := evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z z)) z) z) 3
     let z := evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z z)) z) z) 3
     let z := evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z z)) z) z) 3
     let z := evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z z)) z) z) 3
     evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z z)) z) z) 3) =
      innerCbrt (u256 x) := by
  have hxW : u256 x < WORD_MOD :=
    Nat.mod_lt x (by unfold WORD_MOD; exact Nat.two_pow_pos 256)
  change cbrtCoreEvmBody (u256 x) = innerCbrt (u256 x)
  by_cases hx0 : u256 x = 0
  · rw [hx0]
    exact cbrtCoreEvmBody_eq_innerCbrt_zero
  · have hx : 0 < u256 x := Nat.pos_of_ne_zero hx0
    exact cbrtCoreEvmBody_eq_innerCbrt_pos (u256 x) hxW hx

-- ============================================================================
-- Level 3: Floor correction
-- ============================================================================

theorem innerCbrt_lt_word
    (x : Nat) (hxW : x < WORD_MOD) :
    innerCbrt x < WORD_MOD := by
  have hx256 : x < 2 ^ 256 := by simpa [WORD_MOD] using hxW
  by_cases hx0 : x = 0
  · subst hx0
    simp [innerCbrt_zero, WORD_MOD]
  · have hx : 0 < x := Nat.pos_of_ne_zero hx0
    have hz87 : innerCbrt x < 2 ^ 87 := by
      have hupper := innerCbrt_upper_u256 x hx hx256
      have hm86 : icbrt x < 2 ^ 86 :=
        m_lt_pow86_of_u256 (icbrt x) x (icbrt_cube_le x) hxW
      omega
    exact Nat.lt_of_lt_of_le hz87 (Nat.le_of_lt (two_pow_lt_word 87 (by decide)))

private theorem innerCbrt_sq_lt_word_of_word
    (x : Nat) (hxW : x < WORD_MOD) :
    innerCbrt x * innerCbrt x < WORD_MOD := by
  have hx256 : x < 2 ^ 256 := by simpa [WORD_MOD] using hxW
  by_cases hx0 : x = 0
  · subst hx0
    simp [innerCbrt_zero, WORD_MOD]
  · have hx : 0 < x := Nat.pos_of_ne_zero hx0
    have hz87 : innerCbrt x < 2 ^ 87 := by
      have hupper := innerCbrt_upper_u256 x hx hx256
      have hm86 : icbrt x < 2 ^ 86 :=
        m_lt_pow86_of_u256 (icbrt x) x (icbrt_cube_le x) hxW
      omega
    exact zsq_lt_word_of_lt_87 (innerCbrt x) hz87

private theorem cbrtFloorEvmCorrection_eq_floorCbrt_of_word
    (x : Nat) (hxW : x < WORD_MOD) :
    evmSub (innerCbrt x)
        (evmLt (evmDiv x (evmMul (innerCbrt x) (innerCbrt x))) (innerCbrt x)) =
      floorCbrt x := by
  have hzW : innerCbrt x < WORD_MOD := innerCbrt_lt_word x hxW
  have hzzW : innerCbrt x * innerCbrt x < WORD_MOD :=
    innerCbrt_sq_lt_word_of_word x hxW
  calc evmSub (innerCbrt x)
        (evmLt (evmDiv x (evmMul (innerCbrt x) (innerCbrt x))) (innerCbrt x))
      = normSub (innerCbrt x)
          (normLt (normDiv x (normMul (innerCbrt x) (innerCbrt x))) (innerCbrt x)) :=
        floor_step_evm_eq_norm x (innerCbrt x) hxW hzW hzzW
    _ = floorCbrt x := by
      unfold floorCbrt
      exact floor_correction_norm_eq_if x (innerCbrt x)

theorem cbrtFloorEvmCorrection_eq_floorCbrt
    (x : Nat) :
    evmSub (innerCbrt (u256 x))
        (evmLt
          (evmDiv (u256 x) (evmMul (innerCbrt (u256 x)) (innerCbrt (u256 x))))
          (innerCbrt (u256 x))) =
      floorCbrt (u256 x) := by
  exact cbrtFloorEvmCorrection_eq_floorCbrt_of_word (u256 x)
    (Nat.mod_lt x (by unfold WORD_MOD; exact Nat.two_pow_pos 256))

theorem floorCbrt_lt_word
    (x : Nat) (hxW : x < WORD_MOD) :
    floorCbrt x < WORD_MOD := by
  have hzW : innerCbrt x < WORD_MOD := innerCbrt_lt_word x hxW
  by_cases hlt : x / (innerCbrt x * innerCbrt x) < innerCbrt x
  · simp [floorCbrt, hlt]
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hzW
  · simp [floorCbrt, hlt, hzW]

theorem floorCbrt_correct_u256_eq_all
    (x : Nat) (hx256 : x < 2 ^ 256) :
    floorCbrt x = icbrt x := by
  by_cases hx0 : x = 0
  · subst hx0
    unfold floorCbrt innerCbrt cbrtSeed icbrt icbrtAux
    rw [Nat.log2_zero]
    decide
  · exact floorCbrt_correct_u256 x (Nat.pos_of_ne_zero hx0) hx256

theorem cbrtFloorEvmCorrection_correct
    (x : Nat) (hx : 0 < u256 x) :
    evmSub (innerCbrt (u256 x))
        (evmLt
          (evmDiv (u256 x) (evmMul (innerCbrt (u256 x)) (innerCbrt (u256 x))))
          (innerCbrt (u256 x))) =
      icbrt (u256 x) := by
  rw [cbrtFloorEvmCorrection_eq_floorCbrt]
  exact floorCbrt_correct_u256 (u256 x) hx
    (Nat.mod_lt x (by unfold WORD_MOD; exact Nat.two_pow_pos 256))

theorem cbrtFloorEvmCorrection_eq_icbrt
    (x : Nat) :
    evmSub (innerCbrt (u256 x))
        (evmLt
          (evmDiv (u256 x) (evmMul (innerCbrt (u256 x)) (innerCbrt (u256 x))))
          (innerCbrt (u256 x))) =
      icbrt (u256 x) := by
  rw [cbrtFloorEvmCorrection_eq_floorCbrt]
  exact floorCbrt_correct_u256_eq_all (u256 x)
    (Nat.mod_lt x (by unfold WORD_MOD; exact Nat.two_pow_pos 256))

-- ============================================================================
-- Level 4: cbrtUp
-- ============================================================================

theorem cbrtUpEvmCorrection_eq_cbrtUp256
    (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    evmAdd (innerCbrt x)
        (evmLt (evmMul (innerCbrt x) (evmMul (innerCbrt x) (innerCbrt x))) x) =
      cbrtUp256 x := by
  have hxW : x < WORD_MOD := by simpa [WORD_MOD, cbrtStep, cbrtSeedMultiplier] using hx256
  have hm86 : icbrt x < 2 ^ 86 := m_lt_pow86_of_u256 (icbrt x) x (icbrt_cube_le x) hxW
  have hz87 : innerCbrt x < 2 ^ 87 := by
    have hupper := innerCbrt_upper_u256 x hx hx256
    omega
  have hzW : innerCbrt x < WORD_MOD :=
    Nat.lt_of_lt_of_le hz87 (Nat.le_of_lt (two_pow_lt_word 87 (by decide)))
  have hzzW : innerCbrt x * innerCbrt x < WORD_MOD := zsq_lt_word_of_lt_87 _ hz87
  have hcubeW : innerCbrt x * (innerCbrt x * innerCbrt x) < WORD_MOD := by
    have := CbrtOverflow.innerCbrt_cube_lt_word x hx hx256
    simpa [WORD_MOD, cbrtStep, cbrtSeedMultiplier] using this
  have hmul_zz : evmMul (innerCbrt x) (innerCbrt x) = normMul (innerCbrt x) (innerCbrt x) :=
    evmMul_eq_normMul_of_no_overflow _ _ hzW hzW hzzW
  rw [hmul_zz]
  have hmulLt : normMul (innerCbrt x) (innerCbrt x) < WORD_MOD := by
    simpa [normMul] using hzzW
  have hcube_mul : evmMul (innerCbrt x) (normMul (innerCbrt x) (innerCbrt x)) =
      normMul (innerCbrt x) (normMul (innerCbrt x) (innerCbrt x)) := by
    have hprod : innerCbrt x * normMul (innerCbrt x) (innerCbrt x) < WORD_MOD := by
      simp [normMul]; exact hcubeW
    exact evmMul_eq_normMul_of_no_overflow _ _ hzW hmulLt hprod
  rw [hcube_mul]
  have hcubeLt : normMul (innerCbrt x) (normMul (innerCbrt x) (innerCbrt x)) < WORD_MOD := by
    simp [normMul]; exact hcubeW
  have hlt_eq : evmLt (normMul (innerCbrt x) (normMul (innerCbrt x) (innerCbrt x))) x =
      normLt (normMul (innerCbrt x) (normMul (innerCbrt x) (innerCbrt x))) x :=
    evmLt_eq_normLt_of_u256 _ x hcubeLt hxW
  rw [hlt_eq]
  have hltVal : normLt (normMul (innerCbrt x) (normMul (innerCbrt x) (innerCbrt x))) x ≤ 1 := by
    unfold normLt; split <;> omega
  have hltLt : normLt (normMul (innerCbrt x) (normMul (innerCbrt x) (innerCbrt x))) x < WORD_MOD :=
    Nat.lt_of_le_of_lt hltVal one_lt_word
  have hfinalLt : innerCbrt x + normLt (normMul (innerCbrt x) (normMul (innerCbrt x) (innerCbrt x))) x < WORD_MOD := by
    have h87W : 2 ^ 87 + 1 < WORD_MOD := by unfold WORD_MOD; decide
    calc innerCbrt x + normLt (normMul (innerCbrt x) (normMul (innerCbrt x) (innerCbrt x))) x
        ≤ innerCbrt x + 1 := Nat.add_le_add_left hltVal _
      _ ≤ 2 ^ 87 + 1 := Nat.add_le_add_right (Nat.le_of_lt hz87) _
      _ < WORD_MOD := h87W
  have hadd := evmAdd_eq_normAdd_of_no_overflow _ _ hzW hltLt hfinalLt
  rw [hadd]
  unfold cbrtUp256 normAdd normLt normMul
  split <;> simp_all [Nat.mul_assoc]

theorem cbrtUpEvmCorrection_eq_cbrtUp256_all
    (x : Nat) :
    evmAdd (innerCbrt (u256 x))
        (evmLt
          (evmMul (innerCbrt (u256 x))
            (evmMul (innerCbrt (u256 x)) (innerCbrt (u256 x))))
          (u256 x)) =
      cbrtUp256 (u256 x) := by
  by_cases hx0 : u256 x = 0
  · rw [hx0]
    simp [cbrtUp256, innerCbrt_zero, evmAdd, evmLt, evmMul, u256, WORD_MOD]
  · exact cbrtUpEvmCorrection_eq_cbrtUp256 (u256 x) (Nat.pos_of_ne_zero hx0)
      (Nat.mod_lt x (by unfold WORD_MOD; exact Nat.two_pow_pos 256))

theorem cbrtUp256_lt_word
    (x : Nat) (hxW : x < WORD_MOD) :
    cbrtUp256 x < WORD_MOD := by
  have hx256 : x < 2 ^ 256 := by simpa [WORD_MOD] using hxW
  by_cases hx0 : x = 0
  · subst hx0
    simp [cbrtUp256, innerCbrt_zero, WORD_MOD]
  · have hx : 0 < x := Nat.pos_of_ne_zero hx0
    have hz87 : innerCbrt x < 2 ^ 87 := by
      have hupper := innerCbrt_upper_u256 x hx hx256
      have hm86 : icbrt x < 2 ^ 86 :=
        m_lt_pow86_of_u256 (icbrt x) x (icbrt_cube_le x) hxW
      omega
    have hle : cbrtUp256 x ≤ innerCbrt x + 1 := by
      by_cases hlt : innerCbrt x * innerCbrt x * innerCbrt x < x
      · simp [cbrtUp256, hlt]
      · simp [cbrtUp256, hlt]
    have hbound : innerCbrt x + 1 < WORD_MOD := by
      have h87W : 2 ^ 87 + 1 < WORD_MOD := by unfold WORD_MOD; decide
      omega
    exact Nat.lt_of_le_of_lt hle hbound

-- ============================================================================
-- Level 4b: cbrtUp upper-bound correctness
-- ============================================================================

/-- cbrtUp256 gives a valid upper bound: x ≤ r³. -/
theorem cbrtUp256_upper_bound
    (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    x ≤ cbrtUp256 x * cbrtUp256 x * cbrtUp256 x := by
  let m := icbrt x
  have hmlo : m * m * m ≤ x := icbrt_cube_le x
  have hmhi : x < (m + 1) * (m + 1) * (m + 1) := icbrt_lt_succ_cube x
  have hbr : m ≤ innerCbrt x ∧ innerCbrt x ≤ m + 1 := by
    constructor
    · exact innerCbrt_lower x m hx hmlo
    · exact innerCbrt_upper_u256 x hx hx256
  unfold cbrtUp256
  by_cases hlt : innerCbrt x * innerCbrt x * innerCbrt x < x
  · simp [hlt]
    -- innerCbrt x = m (otherwise (m+1)³ < x, contradicting hmhi)
    have hzm : innerCbrt x = m := by
      have hneq : innerCbrt x ≠ m + 1 := by
        intro hce; rw [hce] at hlt; omega
      omega
    rw [hzm]; exact Nat.le_of_lt hmhi
  · simp [hlt]; exact Nat.le_of_not_gt hlt

-- ============================================================================
-- Level 4c: cbrtUp lower bound (exact ceiling)
-- ============================================================================

/-- cbrtUp256 gives a tight lower bound: (r-1)³ < x.
    Combined with the upper bound (x ≤ r³), this shows r = ⌈∛x⌉. -/
theorem cbrtUp256_lower_bound
    (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    (cbrtUp256 x - 1) * (cbrtUp256 x - 1) * (cbrtUp256 x - 1) < x := by
  have hmlo : icbrt x * icbrt x * icbrt x ≤ x := icbrt_cube_le x
  have hupper : innerCbrt x ≤ icbrt x + 1 := innerCbrt_upper_u256 x hx hx256
  have hlower : icbrt x ≤ innerCbrt x := innerCbrt_lower x (icbrt x) hx hmlo
  unfold cbrtUp256
  by_cases hlt : innerCbrt x * innerCbrt x * innerCbrt x < x
  · -- innerCbrt(x)³ < x: cbrtUp256 = innerCbrt(x) + 1, (innerCbrt(x)+1-1)³ = innerCbrt(x)³ < x
    simp [hlt]
  · -- innerCbrt(x)³ ≥ x: cbrtUp256 = innerCbrt(x)
    simp [hlt]
    -- Need: (innerCbrt(x) - 1)³ < x. Case split: innerCbrt(x) = icbrt(x) or icbrt(x)+1.
    have hcases := innerCbrt_correct_of_upper x hx hupper
    rcases hcases with heqm | heqm1
    · -- innerCbrt(x) = icbrt(x) = m. Need (m-1)³ < x.
      rw [heqm]
      -- m > 0 since x > 0 implies icbrt(x) > 0
      have hm_pos : 0 < icbrt x := by
        by_cases h0 : icbrt x = 0
        · -- icbrt(x) = 0 means 0³ ≤ x < 1³ = 1, so x = 0, contradicting hx > 0.
          have := icbrt_lt_succ_cube x; rw [h0] at this; simp at this; omega
        · exact Nat.pos_of_ne_zero h0
      -- (m-1)³ < m³ ≤ x
      have : (icbrt x - 1) * (icbrt x - 1) * (icbrt x - 1) <
             icbrt x * icbrt x * icbrt x := by
        have hpred : icbrt x - 1 < icbrt x := Nat.sub_lt hm_pos (by omega)
        -- (m-1)³ ≤ (m-1)² * m < m² * m = m³
        calc (icbrt x - 1) * (icbrt x - 1) * (icbrt x - 1)
            ≤ (icbrt x - 1) * (icbrt x - 1) * icbrt x :=
              Nat.mul_le_mul_left _ (Nat.le_of_lt hpred)
          _ ≤ (icbrt x - 1) * icbrt x * icbrt x :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_of_lt hpred))
          _ < icbrt x * icbrt x * icbrt x :=
              Nat.mul_lt_mul_of_pos_right
                (Nat.mul_lt_mul_of_pos_right hpred hm_pos)
                hm_pos
      omega
    · -- innerCbrt(x) = icbrt(x) + 1. Need (icbrt(x))³ < x.
      rw [heqm1]; simp
      -- Since innerCbrt(x) = icbrt(x)+1 and innerCbrt(m³) = m for m = icbrt(x),
      -- x ≠ icbrt(x)³. Combined with icbrt(x)³ ≤ x: strict inequality.
      have hm_pos : 0 < icbrt x := by
        by_cases h0 : icbrt x = 0
        · have := icbrt_lt_succ_cube x; rw [h0] at this; simp at this; omega
        · exact Nat.pos_of_ne_zero h0
      have hx_ne : x ≠ icbrt x * icbrt x * icbrt x := by
        intro hxeq
        have hpc := CbrtWiring.innerCbrt_on_perfect_cube (icbrt x)
          hm_pos (by rw [← hxeq]; exact hx256)
        -- hpc : innerCbrt (icbrt x * icbrt x * icbrt x) = icbrt x
        -- heqm1 : innerCbrt x = icbrt x + 1
        -- From hxeq: x = icbrt x * icbrt x * icbrt x
        have : innerCbrt (icbrt x * icbrt x * icbrt x) = icbrt x + 1 := by
          rwa [← hxeq]
        -- Contradiction: icbrt x = icbrt x + 1
        omega
      omega

/-- `cbrtUp256` gives the exact ceiling cube root for positive uint256 inputs. -/
theorem cbrtUp256_is_ceil
    (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    let r := cbrtUp256 x
    (r - 1) * (r - 1) * (r - 1) < x ∧ x ≤ r * r * r := by
  exact ⟨cbrtUp256_lower_bound x hx hx256,
         cbrtUp256_upper_bound x hx hx256⟩

/-- `cbrtUp256` is correct for all uint256 inputs. -/
theorem cbrtUp256_is_ceil_all
    (x : Nat) (hx256 : x < 2 ^ 256) :
    let r := cbrtUp256 x
    x ≤ r * r * r ∧ (r = 0 ∨ (r - 1) * (r - 1) * (r - 1) < x) := by
  by_cases hx : 0 < x
  · have ⟨hlo, hhi⟩ := cbrtUp256_is_ceil x hx hx256
    exact ⟨hhi, Or.inr hlo⟩
  · simp at hx
    subst hx
    simp [cbrtUp256, innerCbrt_zero]

-- ============================================================================
-- Level 4d: cbrtUp minimality (smallest integer with r³ ≥ x)
-- ============================================================================

/-- If `r = 0` or `(r-1)³ < x`, then `r` is the smallest value whose cube is ≥ x. -/
private theorem minimal_of_pred_cube_lt
    (x r : Nat)
    (hpred : r = 0 ∨ (r - 1) * (r - 1) * (r - 1) < x) :
    ∀ y, x ≤ y * y * y → r ≤ y := by
  intro y hy
  by_cases hry : r ≤ y
  · exact hry
  · have hylt : y < r := Nat.lt_of_not_ge hry
    cases hpred with
    | inl hr0 =>
        exact False.elim ((Nat.not_lt_of_ge hylt) (by simp [hr0]))
    | inr hpredlt =>
        have hyle : y ≤ r - 1 := by omega
        have hycube : y * y * y ≤ (r - 1) * (r - 1) * (r - 1) := cube_monotone hyle
        have hcontra : x ≤ (r - 1) * (r - 1) * (r - 1) := Nat.le_trans hy hycube
        exact False.elim ((Nat.not_lt_of_ge hcontra) hpredlt)

/-- `cbrtUp256` is exactly the smallest integer whose cube is at least `x`. -/
theorem cbrtUp256_ceil_u256
    (x : Nat)
    (hx256 : x < 2 ^ 256) :
    let r := cbrtUp256 x
    x ≤ r * r * r ∧ ∀ y, x ≤ y * y * y → r ≤ y := by
  have hceil := cbrtUp256_is_ceil_all x hx256
  exact ⟨hceil.1, minimal_of_pred_cube_lt x (cbrtUp256 x) hceil.2⟩


end CbrtEvmMath
