/-
  Bridge: auto-generated Lean model of Cbrt.sol ↔ proven-correct hand-written spec.

  Levels:
    1. Nat model = hand-written spec  (normStep, normSeed, model_cbrt ↔ innerCbrt)
    2. EVM model = Nat model           (no overflow on uint256)
    3. Floor correction                 (model_cbrt_floor_evm = floorCbrt = icbrt)
    4. cbrtUp rounding                  (model_cbrt_up_evm rounds up correctly)
-/
import Init
import CbrtProof.CbrtYul
import CbrtProof.CbrtCorrect
import CbrtProof.CertifiedChain
import CbrtProof.FiniteCert
import CbrtProof.Wiring
import CbrtProof.OverflowSafety

set_option exponentiation.threshold 300

namespace CbrtYul

open CbrtYul
open CbrtCertified
open CbrtCert
open CbrtWiring

-- ============================================================================
-- Level 1: Nat model = hand-written spec
-- ============================================================================

/-- One NR step in the generated model unfolds to cbrtStep. -/
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

private theorem model_cbrt_zero : model_cbrt 0 = 0 := by
  decide

private theorem innerCbrt_zero : innerCbrt 0 = 0 := by
  unfold innerCbrt cbrtSeed
  rw [Nat.log2_zero]
  decide

/-- For uint256 inputs, model_cbrt x = innerCbrt x. -/
theorem model_cbrt_eq_innerCbrt (x : Nat) (hx256 : x < 2 ^ 256) :
    model_cbrt x = innerCbrt x := by
  by_cases hx0 : x = 0
  · subst hx0
    rw [model_cbrt_zero, innerCbrt_zero]
  · have hx : 0 < x := Nat.pos_of_ne_zero hx0
    have hseed : normShr 7 (normShl (normDiv (normSub 257 (normClz x)) 3)
        (normAdd 90 (normMul 26 (normMod (normSub 257 (normClz x)) 3)))) =
        cbrtSeed x :=
      normSub257Clz_eq_cbrtSeed_of_pos_u256 x hx hx256
    unfold model_cbrt innerCbrt
    simp [hseed, normStep_eq_cbrtStep]

-- ============================================================================
-- Level 1.5: Bracket result for Nat model
-- ============================================================================

theorem model_cbrt_bracket_u256_all
    (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    let m := icbrt x
    m ≤ model_cbrt x ∧ model_cbrt x ≤ m + 1 := by
  rw [model_cbrt_eq_innerCbrt x hx256]
  constructor
  · exact innerCbrt_lower x (icbrt x) hx (icbrt_cube_le x)
  · exact innerCbrt_upper_u256 x hx hx256

-- ============================================================================
-- Level 2: EVM helpers
-- ============================================================================

private theorem word_mod_gt_256 : 256 < WORD_MOD := by
  unfold WORD_MOD; decide

private theorem u256_eq_of_lt (x : Nat) (hx : x < WORD_MOD) : u256 x = x := by
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
-- Level 2: Full EVM = Nat model
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

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
-- Small x: model_cbrt_evm = model_cbrt for all x < 256.
private theorem small_cbrt_evm_eq : ∀ v : Fin 256,
    model_cbrt_evm v.val = model_cbrt v.val := by
  intro v
  match v with
  | ⟨0, _⟩ =>
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD]
  | ⟨1, _⟩ =>
    have hlog : Nat.log2 1 = 0 :=
      (CbrtCompat.log2_eq_iff (by decide : (1 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨2, _⟩ =>
    have hlog : Nat.log2 2 = 1 :=
      (CbrtCompat.log2_eq_iff (by decide : (2 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨3, _⟩ =>
    have hlog : Nat.log2 3 = 1 :=
      (CbrtCompat.log2_eq_iff (by decide : (3 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨4, _⟩ =>
    have hlog : Nat.log2 4 = 2 :=
      (CbrtCompat.log2_eq_iff (by decide : (4 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨5, _⟩ =>
    have hlog : Nat.log2 5 = 2 :=
      (CbrtCompat.log2_eq_iff (by decide : (5 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨6, _⟩ =>
    have hlog : Nat.log2 6 = 2 :=
      (CbrtCompat.log2_eq_iff (by decide : (6 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨7, _⟩ =>
    have hlog : Nat.log2 7 = 2 :=
      (CbrtCompat.log2_eq_iff (by decide : (7 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨8, _⟩ =>
    have hlog : Nat.log2 8 = 3 :=
      (CbrtCompat.log2_eq_iff (by decide : (8 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨9, _⟩ =>
    have hlog : Nat.log2 9 = 3 :=
      (CbrtCompat.log2_eq_iff (by decide : (9 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨10, _⟩ =>
    have hlog : Nat.log2 10 = 3 :=
      (CbrtCompat.log2_eq_iff (by decide : (10 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨11, _⟩ =>
    have hlog : Nat.log2 11 = 3 :=
      (CbrtCompat.log2_eq_iff (by decide : (11 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨12, _⟩ =>
    have hlog : Nat.log2 12 = 3 :=
      (CbrtCompat.log2_eq_iff (by decide : (12 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨13, _⟩ =>
    have hlog : Nat.log2 13 = 3 :=
      (CbrtCompat.log2_eq_iff (by decide : (13 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨14, _⟩ =>
    have hlog : Nat.log2 14 = 3 :=
      (CbrtCompat.log2_eq_iff (by decide : (14 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨15, _⟩ =>
    have hlog : Nat.log2 15 = 3 :=
      (CbrtCompat.log2_eq_iff (by decide : (15 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨16, _⟩ =>
    have hlog : Nat.log2 16 = 4 :=
      (CbrtCompat.log2_eq_iff (by decide : (16 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨17, _⟩ =>
    have hlog : Nat.log2 17 = 4 :=
      (CbrtCompat.log2_eq_iff (by decide : (17 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨18, _⟩ =>
    have hlog : Nat.log2 18 = 4 :=
      (CbrtCompat.log2_eq_iff (by decide : (18 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨19, _⟩ =>
    have hlog : Nat.log2 19 = 4 :=
      (CbrtCompat.log2_eq_iff (by decide : (19 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨20, _⟩ =>
    have hlog : Nat.log2 20 = 4 :=
      (CbrtCompat.log2_eq_iff (by decide : (20 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨21, _⟩ =>
    have hlog : Nat.log2 21 = 4 :=
      (CbrtCompat.log2_eq_iff (by decide : (21 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨22, _⟩ =>
    have hlog : Nat.log2 22 = 4 :=
      (CbrtCompat.log2_eq_iff (by decide : (22 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨23, _⟩ =>
    have hlog : Nat.log2 23 = 4 :=
      (CbrtCompat.log2_eq_iff (by decide : (23 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨24, _⟩ =>
    have hlog : Nat.log2 24 = 4 :=
      (CbrtCompat.log2_eq_iff (by decide : (24 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨25, _⟩ =>
    have hlog : Nat.log2 25 = 4 :=
      (CbrtCompat.log2_eq_iff (by decide : (25 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨26, _⟩ =>
    have hlog : Nat.log2 26 = 4 :=
      (CbrtCompat.log2_eq_iff (by decide : (26 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨27, _⟩ =>
    have hlog : Nat.log2 27 = 4 :=
      (CbrtCompat.log2_eq_iff (by decide : (27 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨28, _⟩ =>
    have hlog : Nat.log2 28 = 4 :=
      (CbrtCompat.log2_eq_iff (by decide : (28 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨29, _⟩ =>
    have hlog : Nat.log2 29 = 4 :=
      (CbrtCompat.log2_eq_iff (by decide : (29 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨30, _⟩ =>
    have hlog : Nat.log2 30 = 4 :=
      (CbrtCompat.log2_eq_iff (by decide : (30 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨31, _⟩ =>
    have hlog : Nat.log2 31 = 4 :=
      (CbrtCompat.log2_eq_iff (by decide : (31 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨32, _⟩ =>
    have hlog : Nat.log2 32 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (32 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨33, _⟩ =>
    have hlog : Nat.log2 33 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (33 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨34, _⟩ =>
    have hlog : Nat.log2 34 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (34 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨35, _⟩ =>
    have hlog : Nat.log2 35 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (35 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨36, _⟩ =>
    have hlog : Nat.log2 36 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (36 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨37, _⟩ =>
    have hlog : Nat.log2 37 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (37 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨38, _⟩ =>
    have hlog : Nat.log2 38 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (38 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨39, _⟩ =>
    have hlog : Nat.log2 39 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (39 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨40, _⟩ =>
    have hlog : Nat.log2 40 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (40 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨41, _⟩ =>
    have hlog : Nat.log2 41 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (41 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨42, _⟩ =>
    have hlog : Nat.log2 42 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (42 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨43, _⟩ =>
    have hlog : Nat.log2 43 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (43 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨44, _⟩ =>
    have hlog : Nat.log2 44 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (44 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨45, _⟩ =>
    have hlog : Nat.log2 45 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (45 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨46, _⟩ =>
    have hlog : Nat.log2 46 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (46 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨47, _⟩ =>
    have hlog : Nat.log2 47 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (47 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨48, _⟩ =>
    have hlog : Nat.log2 48 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (48 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨49, _⟩ =>
    have hlog : Nat.log2 49 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (49 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨50, _⟩ =>
    have hlog : Nat.log2 50 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (50 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨51, _⟩ =>
    have hlog : Nat.log2 51 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (51 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨52, _⟩ =>
    have hlog : Nat.log2 52 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (52 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨53, _⟩ =>
    have hlog : Nat.log2 53 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (53 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨54, _⟩ =>
    have hlog : Nat.log2 54 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (54 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨55, _⟩ =>
    have hlog : Nat.log2 55 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (55 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨56, _⟩ =>
    have hlog : Nat.log2 56 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (56 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨57, _⟩ =>
    have hlog : Nat.log2 57 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (57 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨58, _⟩ =>
    have hlog : Nat.log2 58 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (58 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨59, _⟩ =>
    have hlog : Nat.log2 59 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (59 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨60, _⟩ =>
    have hlog : Nat.log2 60 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (60 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨61, _⟩ =>
    have hlog : Nat.log2 61 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (61 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨62, _⟩ =>
    have hlog : Nat.log2 62 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (62 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨63, _⟩ =>
    have hlog : Nat.log2 63 = 5 :=
      (CbrtCompat.log2_eq_iff (by decide : (63 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨64, _⟩ =>
    have hlog : Nat.log2 64 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (64 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨65, _⟩ =>
    have hlog : Nat.log2 65 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (65 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨66, _⟩ =>
    have hlog : Nat.log2 66 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (66 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨67, _⟩ =>
    have hlog : Nat.log2 67 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (67 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨68, _⟩ =>
    have hlog : Nat.log2 68 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (68 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨69, _⟩ =>
    have hlog : Nat.log2 69 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (69 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨70, _⟩ =>
    have hlog : Nat.log2 70 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (70 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨71, _⟩ =>
    have hlog : Nat.log2 71 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (71 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨72, _⟩ =>
    have hlog : Nat.log2 72 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (72 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨73, _⟩ =>
    have hlog : Nat.log2 73 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (73 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨74, _⟩ =>
    have hlog : Nat.log2 74 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (74 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨75, _⟩ =>
    have hlog : Nat.log2 75 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (75 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨76, _⟩ =>
    have hlog : Nat.log2 76 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (76 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨77, _⟩ =>
    have hlog : Nat.log2 77 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (77 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨78, _⟩ =>
    have hlog : Nat.log2 78 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (78 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨79, _⟩ =>
    have hlog : Nat.log2 79 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (79 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨80, _⟩ =>
    have hlog : Nat.log2 80 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (80 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨81, _⟩ =>
    have hlog : Nat.log2 81 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (81 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨82, _⟩ =>
    have hlog : Nat.log2 82 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (82 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨83, _⟩ =>
    have hlog : Nat.log2 83 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (83 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨84, _⟩ =>
    have hlog : Nat.log2 84 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (84 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨85, _⟩ =>
    have hlog : Nat.log2 85 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (85 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨86, _⟩ =>
    have hlog : Nat.log2 86 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (86 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨87, _⟩ =>
    have hlog : Nat.log2 87 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (87 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨88, _⟩ =>
    have hlog : Nat.log2 88 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (88 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨89, _⟩ =>
    have hlog : Nat.log2 89 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (89 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨90, _⟩ =>
    have hlog : Nat.log2 90 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (90 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨91, _⟩ =>
    have hlog : Nat.log2 91 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (91 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨92, _⟩ =>
    have hlog : Nat.log2 92 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (92 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨93, _⟩ =>
    have hlog : Nat.log2 93 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (93 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨94, _⟩ =>
    have hlog : Nat.log2 94 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (94 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨95, _⟩ =>
    have hlog : Nat.log2 95 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (95 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨96, _⟩ =>
    have hlog : Nat.log2 96 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (96 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨97, _⟩ =>
    have hlog : Nat.log2 97 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (97 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨98, _⟩ =>
    have hlog : Nat.log2 98 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (98 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨99, _⟩ =>
    have hlog : Nat.log2 99 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (99 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨100, _⟩ =>
    have hlog : Nat.log2 100 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (100 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨101, _⟩ =>
    have hlog : Nat.log2 101 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (101 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨102, _⟩ =>
    have hlog : Nat.log2 102 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (102 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨103, _⟩ =>
    have hlog : Nat.log2 103 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (103 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨104, _⟩ =>
    have hlog : Nat.log2 104 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (104 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨105, _⟩ =>
    have hlog : Nat.log2 105 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (105 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨106, _⟩ =>
    have hlog : Nat.log2 106 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (106 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨107, _⟩ =>
    have hlog : Nat.log2 107 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (107 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨108, _⟩ =>
    have hlog : Nat.log2 108 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (108 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨109, _⟩ =>
    have hlog : Nat.log2 109 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (109 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨110, _⟩ =>
    have hlog : Nat.log2 110 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (110 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨111, _⟩ =>
    have hlog : Nat.log2 111 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (111 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨112, _⟩ =>
    have hlog : Nat.log2 112 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (112 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨113, _⟩ =>
    have hlog : Nat.log2 113 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (113 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨114, _⟩ =>
    have hlog : Nat.log2 114 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (114 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨115, _⟩ =>
    have hlog : Nat.log2 115 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (115 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨116, _⟩ =>
    have hlog : Nat.log2 116 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (116 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨117, _⟩ =>
    have hlog : Nat.log2 117 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (117 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨118, _⟩ =>
    have hlog : Nat.log2 118 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (118 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨119, _⟩ =>
    have hlog : Nat.log2 119 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (119 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨120, _⟩ =>
    have hlog : Nat.log2 120 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (120 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨121, _⟩ =>
    have hlog : Nat.log2 121 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (121 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨122, _⟩ =>
    have hlog : Nat.log2 122 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (122 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨123, _⟩ =>
    have hlog : Nat.log2 123 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (123 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨124, _⟩ =>
    have hlog : Nat.log2 124 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (124 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨125, _⟩ =>
    have hlog : Nat.log2 125 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (125 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨126, _⟩ =>
    have hlog : Nat.log2 126 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (126 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨127, _⟩ =>
    have hlog : Nat.log2 127 = 6 :=
      (CbrtCompat.log2_eq_iff (by decide : (127 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨128, _⟩ =>
    have hlog : Nat.log2 128 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (128 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨129, _⟩ =>
    have hlog : Nat.log2 129 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (129 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨130, _⟩ =>
    have hlog : Nat.log2 130 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (130 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨131, _⟩ =>
    have hlog : Nat.log2 131 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (131 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨132, _⟩ =>
    have hlog : Nat.log2 132 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (132 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨133, _⟩ =>
    have hlog : Nat.log2 133 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (133 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨134, _⟩ =>
    have hlog : Nat.log2 134 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (134 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨135, _⟩ =>
    have hlog : Nat.log2 135 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (135 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨136, _⟩ =>
    have hlog : Nat.log2 136 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (136 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨137, _⟩ =>
    have hlog : Nat.log2 137 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (137 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨138, _⟩ =>
    have hlog : Nat.log2 138 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (138 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨139, _⟩ =>
    have hlog : Nat.log2 139 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (139 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨140, _⟩ =>
    have hlog : Nat.log2 140 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (140 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨141, _⟩ =>
    have hlog : Nat.log2 141 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (141 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨142, _⟩ =>
    have hlog : Nat.log2 142 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (142 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨143, _⟩ =>
    have hlog : Nat.log2 143 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (143 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨144, _⟩ =>
    have hlog : Nat.log2 144 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (144 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨145, _⟩ =>
    have hlog : Nat.log2 145 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (145 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨146, _⟩ =>
    have hlog : Nat.log2 146 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (146 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨147, _⟩ =>
    have hlog : Nat.log2 147 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (147 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨148, _⟩ =>
    have hlog : Nat.log2 148 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (148 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨149, _⟩ =>
    have hlog : Nat.log2 149 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (149 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨150, _⟩ =>
    have hlog : Nat.log2 150 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (150 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨151, _⟩ =>
    have hlog : Nat.log2 151 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (151 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨152, _⟩ =>
    have hlog : Nat.log2 152 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (152 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨153, _⟩ =>
    have hlog : Nat.log2 153 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (153 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨154, _⟩ =>
    have hlog : Nat.log2 154 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (154 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨155, _⟩ =>
    have hlog : Nat.log2 155 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (155 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨156, _⟩ =>
    have hlog : Nat.log2 156 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (156 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨157, _⟩ =>
    have hlog : Nat.log2 157 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (157 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨158, _⟩ =>
    have hlog : Nat.log2 158 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (158 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨159, _⟩ =>
    have hlog : Nat.log2 159 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (159 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨160, _⟩ =>
    have hlog : Nat.log2 160 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (160 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨161, _⟩ =>
    have hlog : Nat.log2 161 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (161 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨162, _⟩ =>
    have hlog : Nat.log2 162 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (162 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨163, _⟩ =>
    have hlog : Nat.log2 163 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (163 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨164, _⟩ =>
    have hlog : Nat.log2 164 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (164 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨165, _⟩ =>
    have hlog : Nat.log2 165 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (165 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨166, _⟩ =>
    have hlog : Nat.log2 166 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (166 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨167, _⟩ =>
    have hlog : Nat.log2 167 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (167 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨168, _⟩ =>
    have hlog : Nat.log2 168 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (168 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨169, _⟩ =>
    have hlog : Nat.log2 169 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (169 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨170, _⟩ =>
    have hlog : Nat.log2 170 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (170 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨171, _⟩ =>
    have hlog : Nat.log2 171 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (171 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨172, _⟩ =>
    have hlog : Nat.log2 172 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (172 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨173, _⟩ =>
    have hlog : Nat.log2 173 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (173 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨174, _⟩ =>
    have hlog : Nat.log2 174 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (174 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨175, _⟩ =>
    have hlog : Nat.log2 175 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (175 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨176, _⟩ =>
    have hlog : Nat.log2 176 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (176 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨177, _⟩ =>
    have hlog : Nat.log2 177 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (177 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨178, _⟩ =>
    have hlog : Nat.log2 178 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (178 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨179, _⟩ =>
    have hlog : Nat.log2 179 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (179 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨180, _⟩ =>
    have hlog : Nat.log2 180 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (180 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨181, _⟩ =>
    have hlog : Nat.log2 181 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (181 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨182, _⟩ =>
    have hlog : Nat.log2 182 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (182 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨183, _⟩ =>
    have hlog : Nat.log2 183 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (183 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨184, _⟩ =>
    have hlog : Nat.log2 184 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (184 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨185, _⟩ =>
    have hlog : Nat.log2 185 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (185 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨186, _⟩ =>
    have hlog : Nat.log2 186 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (186 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨187, _⟩ =>
    have hlog : Nat.log2 187 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (187 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨188, _⟩ =>
    have hlog : Nat.log2 188 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (188 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨189, _⟩ =>
    have hlog : Nat.log2 189 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (189 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨190, _⟩ =>
    have hlog : Nat.log2 190 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (190 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨191, _⟩ =>
    have hlog : Nat.log2 191 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (191 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨192, _⟩ =>
    have hlog : Nat.log2 192 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (192 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨193, _⟩ =>
    have hlog : Nat.log2 193 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (193 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨194, _⟩ =>
    have hlog : Nat.log2 194 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (194 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨195, _⟩ =>
    have hlog : Nat.log2 195 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (195 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨196, _⟩ =>
    have hlog : Nat.log2 196 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (196 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨197, _⟩ =>
    have hlog : Nat.log2 197 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (197 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨198, _⟩ =>
    have hlog : Nat.log2 198 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (198 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨199, _⟩ =>
    have hlog : Nat.log2 199 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (199 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨200, _⟩ =>
    have hlog : Nat.log2 200 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (200 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨201, _⟩ =>
    have hlog : Nat.log2 201 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (201 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨202, _⟩ =>
    have hlog : Nat.log2 202 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (202 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨203, _⟩ =>
    have hlog : Nat.log2 203 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (203 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨204, _⟩ =>
    have hlog : Nat.log2 204 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (204 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨205, _⟩ =>
    have hlog : Nat.log2 205 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (205 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨206, _⟩ =>
    have hlog : Nat.log2 206 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (206 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨207, _⟩ =>
    have hlog : Nat.log2 207 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (207 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨208, _⟩ =>
    have hlog : Nat.log2 208 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (208 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨209, _⟩ =>
    have hlog : Nat.log2 209 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (209 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨210, _⟩ =>
    have hlog : Nat.log2 210 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (210 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨211, _⟩ =>
    have hlog : Nat.log2 211 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (211 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨212, _⟩ =>
    have hlog : Nat.log2 212 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (212 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨213, _⟩ =>
    have hlog : Nat.log2 213 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (213 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨214, _⟩ =>
    have hlog : Nat.log2 214 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (214 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨215, _⟩ =>
    have hlog : Nat.log2 215 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (215 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨216, _⟩ =>
    have hlog : Nat.log2 216 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (216 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨217, _⟩ =>
    have hlog : Nat.log2 217 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (217 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨218, _⟩ =>
    have hlog : Nat.log2 218 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (218 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨219, _⟩ =>
    have hlog : Nat.log2 219 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (219 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨220, _⟩ =>
    have hlog : Nat.log2 220 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (220 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨221, _⟩ =>
    have hlog : Nat.log2 221 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (221 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨222, _⟩ =>
    have hlog : Nat.log2 222 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (222 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨223, _⟩ =>
    have hlog : Nat.log2 223 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (223 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨224, _⟩ =>
    have hlog : Nat.log2 224 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (224 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨225, _⟩ =>
    have hlog : Nat.log2 225 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (225 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨226, _⟩ =>
    have hlog : Nat.log2 226 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (226 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨227, _⟩ =>
    have hlog : Nat.log2 227 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (227 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨228, _⟩ =>
    have hlog : Nat.log2 228 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (228 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨229, _⟩ =>
    have hlog : Nat.log2 229 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (229 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨230, _⟩ =>
    have hlog : Nat.log2 230 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (230 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨231, _⟩ =>
    have hlog : Nat.log2 231 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (231 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨232, _⟩ =>
    have hlog : Nat.log2 232 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (232 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨233, _⟩ =>
    have hlog : Nat.log2 233 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (233 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨234, _⟩ =>
    have hlog : Nat.log2 234 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (234 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨235, _⟩ =>
    have hlog : Nat.log2 235 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (235 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨236, _⟩ =>
    have hlog : Nat.log2 236 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (236 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨237, _⟩ =>
    have hlog : Nat.log2 237 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (237 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨238, _⟩ =>
    have hlog : Nat.log2 238 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (238 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨239, _⟩ =>
    have hlog : Nat.log2 239 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (239 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨240, _⟩ =>
    have hlog : Nat.log2 240 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (240 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨241, _⟩ =>
    have hlog : Nat.log2 241 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (241 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨242, _⟩ =>
    have hlog : Nat.log2 242 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (242 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨243, _⟩ =>
    have hlog : Nat.log2 243 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (243 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨244, _⟩ =>
    have hlog : Nat.log2 244 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (244 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨245, _⟩ =>
    have hlog : Nat.log2 245 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (245 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨246, _⟩ =>
    have hlog : Nat.log2 246 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (246 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨247, _⟩ =>
    have hlog : Nat.log2 247 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (247 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨248, _⟩ =>
    have hlog : Nat.log2 248 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (248 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨249, _⟩ =>
    have hlog : Nat.log2 249 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (249 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨250, _⟩ =>
    have hlog : Nat.log2 250 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (250 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨251, _⟩ =>
    have hlog : Nat.log2 251 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (251 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨252, _⟩ =>
    have hlog : Nat.log2 252 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (252 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨253, _⟩ =>
    have hlog : Nat.log2 253 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (253 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨254, _⟩ =>
    have hlog : Nat.log2 254 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (254 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨255, _⟩ =>
    have hlog : Nat.log2 255 = 7 :=
      (CbrtCompat.log2_eq_iff (by decide : (255 : Nat) ≠ 0)).2 ⟨by decide, by decide⟩
    simp [model_cbrt_evm, model_cbrt, evmSub, evmClz, normClz, evmShr, evmShl,
        evmDiv, evmAdd, evmMul, evmMod, u256, normShr, normShl, normDiv, normAdd,
        normMul, normMod, normSub, WORD_MOD, hlog]
  | ⟨_ + 256, h⟩ => omega

theorem model_cbrt_evm_eq_model_cbrt
    (x : Nat)
    (hx256 : x < WORD_MOD) :
    model_cbrt_evm x = model_cbrt x := by
  by_cases hx0 : x = 0
  · subst hx0
    exact small_cbrt_evm_eq ⟨0, by decide⟩
  · have hx : 0 < x := Nat.pos_of_ne_zero hx0
    by_cases hx_small : x < 256
    · exact small_cbrt_evm_eq ⟨x, hx_small⟩
    · -- x ≥ 256: use certificate approach
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
      -- Lower bounds via floor bound
      have hmz1 : m ≤ z1 := by
        dsimp [z1, z0]
        exact cbrt_step_floor_bound x (seedOf idx) m hsPos hmlo
      have hz1Pos : 0 < z1 := Nat.lt_of_lt_of_le hm hmz1
      have hmz2 : m ≤ z2 := by
        dsimp [z2]; exact cbrt_step_floor_bound x z1 m hz1Pos hmlo
      have hz2Pos : 0 < z2 := Nat.lt_of_lt_of_le hm hmz2
      have hmz3 : m ≤ z3 := by
        dsimp [z3]; exact cbrt_step_floor_bound x z2 m hz2Pos hmlo
      have hz3Pos : 0 < z3 := Nat.lt_of_lt_of_le hm hmz3
      have hmz4 : m ≤ z4 := by
        dsimp [z4]; exact cbrt_step_floor_bound x z3 m hz3Pos hmlo
      have hz4Pos : 0 < z4 := Nat.lt_of_lt_of_le hm hmz4
      -- Error bounds from certificate chain
      have hm2 : 2 ≤ m := Nat.le_trans (lo_ge_two idx) hinterval.1
      have hloPos : 0 < loOf idx := lo_pos idx
      -- Step 1: d1 bound from analytic formula
      have hd1 : z1 - m ≤ d1Of idx := by
        have h := CbrtCertified.cbrt_d1_bound x m (seedOf idx) (loOf idx) (hiOf idx)
          hsPos hmlo hmhi hinterval.1 hinterval.2
        simp only at h
        show cbrtStep x (seedOf idx) - m ≤ d1Of idx
        have hd1eq := d1_eq idx
        have hmaxeq := maxabs_eq idx
        rw [hmaxeq] at hd1eq
        rw [← hd1eq] at h
        exact h
      have h2d1 : 2 * d1Of idx ≤ m := Nat.le_trans (two_d1_le_lo idx) hinterval.1
      -- Steps 2-5 via step_from_bound
      have hd2 : z2 - m ≤ d2Of idx := by
        have h := CbrtCertified.step_from_bound x m (loOf idx) z1 (d1Of idx) hm2 hloPos
          hinterval.1 hmhi hmz1 hd1 h2d1
        show cbrtStep x z1 - m ≤ d2Of idx; unfold d2Of; exact h
      have h2d2 : 2 * d2Of idx ≤ m := Nat.le_trans (two_d2_le_lo idx) hinterval.1
      have hd3 : z3 - m ≤ d3Of idx := by
        have h := CbrtCertified.step_from_bound x m (loOf idx) z2 (d2Of idx) hm2 hloPos
          hinterval.1 hmhi hmz2 hd2 h2d2
        show cbrtStep x z2 - m ≤ d3Of idx; unfold d3Of; exact h
      have h2d3 : 2 * d3Of idx ≤ m := Nat.le_trans (two_d3_le_lo idx) hinterval.1
      have hd4 : z4 - m ≤ d4Of idx := by
        have h := CbrtCertified.step_from_bound x m (loOf idx) z3 (d3Of idx) hm2 hloPos
          hinterval.1 hmhi hmz3 hd3 h2d3
        show cbrtStep x z3 - m ≤ d4Of idx; unfold d4Of; exact h
      have h2d4 : 2 * d4Of idx ≤ m := Nat.le_trans (two_d4_le_lo idx) hinterval.1
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
        cbrt_sum_lt_word_of_bounds x m z1 hx256 hm hmlo hmhi hmz1 hz1_le_2m
      have hsum2 : x / (z2 * z2) + 2 * z2 < WORD_MOD :=
        cbrt_sum_lt_word_of_bounds x m z2 hx256 hm hmlo hmhi hmz2 hz2_le_2m
      have hsum3 : x / (z3 * z3) + 2 * z3 < WORD_MOD :=
        cbrt_sum_lt_word_of_bounds x m z3 hx256 hm hmlo hmhi hmz3 hz3_le_2m
      have hsum4 : x / (z4 * z4) + 2 * z4 < WORD_MOD :=
        cbrt_sum_lt_word_of_bounds x m z4 hx256 hm hmlo hmhi hmz4 hz4_le_2m
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
      have hseedNorm :
          normShr 7 (normShl (normDiv (normSub 257 (normClz x)) 3)
            (normAdd 90 (normMul 26 (normMod (normSub 257 (normClz x)) 3)))) =
            seedOf idx := by
        exact (normSub257Clz_eq_cbrtSeed_of_pos_u256 x hx hx256).trans hseedOf
      have hseedEvm :
          evmShr 7 (evmShl (evmDiv (evmSub 257 (evmClz x)) 3)
            (evmAdd 90 (evmMul 26 (evmMod (evmSub 257 (evmClz x)) 3)))) =
            seedOf idx := by
        have hOldNorm := (normSub257Clz_eq_cbrtSeed_of_pos_u256 x hx hx256).trans hseedOf
        exact (seed_evm_eq_norm x hx hx256).trans hOldNorm
      -- Final assembly
      have hxmod : u256 x = x := u256_eq_of_lt x hx256
      unfold model_cbrt_evm model_cbrt
      simp [hxmod, hseedEvm, hseedNorm, z0, z1, z2, z3, z4, z5,
        hstep1, hstep2, hstep3, hstep4, hstep5, normStep_eq_cbrtStep]

-- Bracket result for the EVM model
theorem model_cbrt_evm_bracket_u256_all
    (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    let m := icbrt x
    m ≤ model_cbrt_evm x ∧ model_cbrt_evm x ≤ m + 1 := by
  have hxW : x < WORD_MOD := by simpa [WORD_MOD] using hx256
  simpa [model_cbrt_evm_eq_model_cbrt x hxW] using model_cbrt_bracket_u256_all x hx hx256

-- ============================================================================
-- Level 3: Floor correction
-- ============================================================================

private theorem floor_correction_norm_eq_if (x z : Nat) :
    normSub z (normLt (normDiv x (normMul z z)) z) =
      (if x / (z * z) < z then z - 1 else z) := by
  by_cases hz0 : z = 0
  · subst hz0; simp [normSub, normLt, normDiv, normMul]
  · by_cases hlt : x / (z * z) < z
    · simp [normSub, normLt, normDiv, normMul, hlt]
    · simp [normSub, normLt, normDiv, normMul, hlt]

theorem model_cbrt_floor_eq_floorCbrt
    (x : Nat) (hx256 : x < 2 ^ 256) :
    model_cbrt_floor x = floorCbrt x := by
  have hinner : model_cbrt x = innerCbrt x := model_cbrt_eq_innerCbrt x hx256
  unfold model_cbrt_floor floorCbrt
  simp [hinner, floor_correction_norm_eq_if]

private theorem normLt_div_zsq_le (x z : Nat) :
    normLt (normDiv x (normMul z z)) z ≤ z := by
  by_cases hz0 : z = 0
  · simp [normLt, normDiv, normMul, hz0]
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
    rw [hmul]; exact evmDiv_eq_normDiv_of_u256 x (normMul z z) hx hmulLt
  have hdivLt : normDiv x (normMul z z) < WORD_MOD :=
    Nat.lt_of_le_of_lt (by simp [normDiv, normMul]; exact Nat.div_le_self _ _) hx
  have hlt : evmLt (evmDiv x (evmMul z z)) z = normLt (normDiv x (normMul z z)) z := by
    simpa [hdiv] using evmLt_eq_normLt_of_u256 (normDiv x (normMul z z)) z hdivLt hz
  have hbLe : normLt (normDiv x (normMul z z)) z ≤ z := normLt_div_zsq_le x z
  calc evmSub z (evmLt (evmDiv x (evmMul z z)) z)
      = evmSub z (normLt (normDiv x (normMul z z)) z) := by rw [hlt]
    _ = normSub z (normLt (normDiv x (normMul z z)) z) :=
        evmSub_eq_normSub_of_le z (normLt (normDiv x (normMul z z)) z) hz hbLe

theorem model_cbrt_floor_evm_eq_model_cbrt_floor
    (x : Nat) (hxW : x < WORD_MOD) :
    model_cbrt_floor_evm x = model_cbrt_floor x := by
  have hx256 : x < 2 ^ 256 := by simpa [WORD_MOD] using hxW
  have hxmod : u256 x = x := u256_eq_of_lt x hxW
  by_cases hx0 : x = 0
  · subst hx0
    have hmodel := model_cbrt_evm_eq_model_cbrt 0 (by unfold WORD_MOD; decide)
    unfold model_cbrt_floor_evm model_cbrt_floor
    simp [u256, WORD_MOD]
    rw [hmodel, model_cbrt_zero]
    simp [evmSub, evmLt, evmDiv, evmMul, normSub, normLt, normDiv, normMul, u256, WORD_MOD]
  · have hx : 0 < x := Nat.pos_of_ne_zero hx0
    have hbr := model_cbrt_evm_bracket_u256_all x hx hx256
    have hm86 : icbrt x < 2 ^ 86 := m_lt_pow86_of_u256 (icbrt x) x (icbrt_cube_le x) hxW
    have hz87 : model_cbrt_evm x < 2 ^ 87 := by
      have : model_cbrt_evm x ≤ icbrt x + 1 := hbr.2; omega
    have hzW : model_cbrt_evm x < WORD_MOD :=
      Nat.lt_of_lt_of_le hz87 (Nat.le_of_lt (two_pow_lt_word 87 (by decide)))
    have hzzW : model_cbrt_evm x * model_cbrt_evm x < WORD_MOD :=
      zsq_lt_word_of_lt_87 (model_cbrt_evm x) hz87
    have hroot : model_cbrt_evm x = model_cbrt x := model_cbrt_evm_eq_model_cbrt x hxW
    unfold model_cbrt_floor_evm model_cbrt_floor
    simp [hxmod]
    simpa [hroot] using floor_step_evm_eq_norm x (model_cbrt_evm x) hxW hzW hzzW

theorem model_cbrt_floor_evm_eq_floorCbrt
    (x : Nat) (hx256 : x < 2 ^ 256) :
    model_cbrt_floor_evm x = floorCbrt x := by
  have hxW : x < WORD_MOD := by simpa [WORD_MOD] using hx256
  calc model_cbrt_floor_evm x
      = model_cbrt_floor x := model_cbrt_floor_evm_eq_model_cbrt_floor x hxW
    _ = floorCbrt x := model_cbrt_floor_eq_floorCbrt x hx256

-- Combined with Wiring's floorCbrt_correct_u256:
theorem model_cbrt_floor_evm_correct
    (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    model_cbrt_floor_evm x = icbrt x := by
  calc model_cbrt_floor_evm x
      = floorCbrt x := model_cbrt_floor_evm_eq_floorCbrt x hx256
    _ = icbrt x := floorCbrt_correct_u256 x hx hx256

-- ============================================================================
-- Level 4: cbrtUp
-- ============================================================================

/-- Specification-level model for `cbrtUp`: round `innerCbrt` upward if needed. -/
def cbrtUpSpec (x : Nat) : Nat :=
  let z := innerCbrt x
  if z * z * z < x then z + 1 else z

-- The Nat-level cbrtUp spec equivalence.
-- The product expression satisfies z * (z * z) = z * z * z by associativity,
-- so normLt(normMul z (normMul z z), x) = if z*z*z < x then 1 else 0.
private theorem model_cbrt_up_norm_eq_cbrtUpSpec
    (x : Nat) (hx256 : x < 2 ^ 256) :
    model_cbrt_up x = cbrtUpSpec x := by
  have hinner : model_cbrt x = innerCbrt x := model_cbrt_eq_innerCbrt x hx256
  unfold model_cbrt_up cbrtUpSpec
  simp only [hinner, normAdd, normLt, normMul, Nat.mul_assoc]
  -- Both sides have z*(z*z). Just need: z + (if _ then 1 else 0) = if _ then z+1 else z
  split <;> simp_all

theorem model_cbrt_up_eq_cbrtUpSpec
    (x : Nat) (hx256 : x < 2 ^ 256) :
    model_cbrt_up x = cbrtUpSpec x :=
  model_cbrt_up_norm_eq_cbrtUpSpec x hx256

-- EVM cbrtUp = cbrtUpSpec.
-- Key overflow facts for the new model (z + lt(mul(z, mul(z, z)), x)):
--   z = model_cbrt_evm x ∈ [m, m+1], m < 2^86, so z < 2^87
--   z² < 2^174 < 2^256  (no overflow in inner mul)
--   z³ < 2^256 (proven in OverflowSafety via innerCbrt_cube_lt_word)
--   lt(...) ≤ 1, z + 1 < 2^87 + 1 < 2^256  (no overflow in final add)
theorem model_cbrt_up_evm_eq_cbrtUpSpec
    (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    model_cbrt_up_evm x = cbrtUpSpec x := by
  -- Strategy: show model_cbrt_up_evm x = model_cbrt_up x, then use the Nat proof.
  have hxW : x < WORD_MOD := by simpa [WORD_MOD] using hx256
  have hroot : model_cbrt_evm x = model_cbrt x := model_cbrt_evm_eq_model_cbrt x hxW
  have hxmod : u256 x = x := u256_eq_of_lt x hxW
  have hinner : model_cbrt x = innerCbrt x := model_cbrt_eq_innerCbrt x hx256
  have hbr := model_cbrt_evm_bracket_u256_all x hx hx256
  have hm86 : icbrt x < 2 ^ 86 := m_lt_pow86_of_u256 (icbrt x) x (icbrt_cube_le x) hxW
  have hz87 : innerCbrt x < 2 ^ 87 := by
    have := hbr.2; rw [hroot, hinner] at this; omega
  have hzW : innerCbrt x < WORD_MOD :=
    Nat.lt_of_lt_of_le hz87 (Nat.le_of_lt (two_pow_lt_word 87 (by decide)))
  have hzzW : innerCbrt x * innerCbrt x < WORD_MOD := zsq_lt_word_of_lt_87 _ hz87
  -- z * (z * z) < WORD_MOD (the key new overflow fact)
  have hcubeW : innerCbrt x * (innerCbrt x * innerCbrt x) < WORD_MOD := by
    have := CbrtOverflow.innerCbrt_cube_lt_word x hx hx256
    simpa [WORD_MOD] using this
  have hup_nat : model_cbrt_up x = cbrtUpSpec x :=
    model_cbrt_up_norm_eq_cbrtUpSpec x hx256
  -- Show model_cbrt_up_evm x = model_cbrt_up x.
  suffices h : model_cbrt_up_evm x = model_cbrt_up x by rw [h]; exact hup_nat
  unfold model_cbrt_up_evm model_cbrt_up
  simp only [hxmod, hroot, hinner]
  -- Goal: evmAdd z (evmLt (evmMul z (evmMul z z)) x)
  --     = normAdd z (normLt (normMul z (normMul z z)) x)
  -- where z = innerCbrt x.
  -- 1. evmMul z z = normMul z z (z² < WORD_MOD)
  have hmul_zz : evmMul (innerCbrt x) (innerCbrt x) = normMul (innerCbrt x) (innerCbrt x) :=
    evmMul_eq_normMul_of_no_overflow _ _ hzW hzW hzzW
  rw [hmul_zz]
  -- 2. evmMul z (normMul z z) = normMul z (normMul z z) (z³ < WORD_MOD)
  have hmulLt : normMul (innerCbrt x) (innerCbrt x) < WORD_MOD := by
    simpa [normMul] using hzzW
  have hcube_mul : evmMul (innerCbrt x) (normMul (innerCbrt x) (innerCbrt x)) =
      normMul (innerCbrt x) (normMul (innerCbrt x) (innerCbrt x)) := by
    have hprod : innerCbrt x * normMul (innerCbrt x) (innerCbrt x) < WORD_MOD := by
      simp [normMul]; exact hcubeW
    exact evmMul_eq_normMul_of_no_overflow _ _ hzW hmulLt hprod
  rw [hcube_mul]
  -- 3. evmLt (normMul z (normMul z z)) x = normLt (normMul z (normMul z z)) x
  have hcubeLt : normMul (innerCbrt x) (normMul (innerCbrt x) (innerCbrt x)) < WORD_MOD := by
    simp [normMul]; exact hcubeW
  have hlt_eq : evmLt (normMul (innerCbrt x) (normMul (innerCbrt x) (innerCbrt x))) x =
      normLt (normMul (innerCbrt x) (normMul (innerCbrt x) (innerCbrt x))) x :=
    evmLt_eq_normLt_of_u256 _ x hcubeLt hxW
  rw [hlt_eq]
  -- 4. evmAdd z (normLt ...) = normAdd z (normLt ...)
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
  exact evmAdd_eq_normAdd_of_no_overflow _ _ hzW hltLt hfinalLt

-- ============================================================================
-- Level 4b: cbrtUp upper-bound correctness
-- ============================================================================

/-- cbrtUpSpec gives a valid upper bound: x ≤ r³. -/
theorem cbrtUpSpec_upper_bound
    (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    x ≤ cbrtUpSpec x * cbrtUpSpec x * cbrtUpSpec x := by
  let m := icbrt x
  have hmlo : m * m * m ≤ x := icbrt_cube_le x
  have hmhi : x < (m + 1) * (m + 1) * (m + 1) := icbrt_lt_succ_cube x
  have hbr : m ≤ innerCbrt x ∧ innerCbrt x ≤ m + 1 := by
    constructor
    · exact innerCbrt_lower x m hx hmlo
    · exact innerCbrt_upper_u256 x hx hx256
  unfold cbrtUpSpec
  by_cases hlt : innerCbrt x * innerCbrt x * innerCbrt x < x
  · simp [hlt]
    -- innerCbrt x = m (otherwise (m+1)³ < x, contradicting hmhi)
    have hzm : innerCbrt x = m := by
      have hneq : innerCbrt x ≠ m + 1 := by
        intro hce; rw [hce] at hlt; omega
      omega
    rw [hzm]; exact Nat.le_of_lt hmhi
  · simp [hlt]; exact Nat.le_of_not_gt hlt

theorem model_cbrt_up_evm_upper_bound
    (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    x ≤ model_cbrt_up_evm x * model_cbrt_up_evm x * model_cbrt_up_evm x := by
  rw [model_cbrt_up_evm_eq_cbrtUpSpec x hx hx256]
  exact cbrtUpSpec_upper_bound x hx hx256

-- ============================================================================
-- Level 4c: cbrtUp lower bound (exact ceiling)
-- ============================================================================

/-- cbrtUpSpec gives a tight lower bound: (r-1)³ < x.
    Combined with the upper bound (x ≤ r³), this shows r = ⌈∛x⌉. -/
theorem cbrtUpSpec_lower_bound
    (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    (cbrtUpSpec x - 1) * (cbrtUpSpec x - 1) * (cbrtUpSpec x - 1) < x := by
  have hmlo : icbrt x * icbrt x * icbrt x ≤ x := icbrt_cube_le x
  have hupper : innerCbrt x ≤ icbrt x + 1 := innerCbrt_upper_u256 x hx hx256
  have hlower : icbrt x ≤ innerCbrt x := innerCbrt_lower x (icbrt x) hx hmlo
  unfold cbrtUpSpec
  by_cases hlt : innerCbrt x * innerCbrt x * innerCbrt x < x
  · -- innerCbrt(x)³ < x: cbrtUpSpec = innerCbrt(x) + 1, (innerCbrt(x)+1-1)³ = innerCbrt(x)³ < x
    simp [hlt]
  · -- innerCbrt(x)³ ≥ x: cbrtUpSpec = innerCbrt(x)
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

/-- The EVM cbrtUp model gives a tight lower bound: (r-1)³ < x. -/
theorem model_cbrt_up_evm_lower_bound
    (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    (model_cbrt_up_evm x - 1) * (model_cbrt_up_evm x - 1) * (model_cbrt_up_evm x - 1) < x := by
  rw [model_cbrt_up_evm_eq_cbrtUpSpec x hx hx256]
  exact cbrtUpSpec_lower_bound x hx hx256

/-- Combined: the EVM cbrtUp model gives the exact ceiling cube root. -/
theorem model_cbrt_up_evm_is_ceil
    (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    let r := model_cbrt_up_evm x
    (r - 1) * (r - 1) * (r - 1) < x ∧ x ≤ r * r * r := by
  exact ⟨model_cbrt_up_evm_lower_bound x hx hx256,
         model_cbrt_up_evm_upper_bound x hx hx256⟩

/-- cbrtUp is correct for ALL x < 2^256 (including x = 0). -/
theorem model_cbrt_up_evm_is_ceil_all
    (x : Nat) (hx256 : x < 2 ^ 256) :
    let r := model_cbrt_up_evm x
    x ≤ r * r * r ∧ (r = 0 ∨ (r - 1) * (r - 1) * (r - 1) < x) := by
  by_cases hx : 0 < x
  · have ⟨hlo, hhi⟩ := model_cbrt_up_evm_is_ceil x hx hx256
    exact ⟨hhi, Or.inr hlo⟩
  · simp at hx
    subst hx
    decide

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

/-- `cbrtUp` is exactly the smallest integer whose cube is ≥ x.
    Matches the sqrt analog `model_sqrt_up_evm_ceil_u256`. -/
theorem model_cbrt_up_evm_ceil_u256
    (x : Nat)
    (hx256 : x < 2 ^ 256) :
    let r := model_cbrt_up_evm x
    x ≤ r * r * r ∧ ∀ y, x ≤ y * y * y → r ≤ y := by
  have hceil := model_cbrt_up_evm_is_ceil_all x hx256
  exact ⟨hceil.1, minimal_of_pred_cube_lt x (model_cbrt_up_evm x) hceil.2⟩

-- ============================================================================
-- Summary
-- ============================================================================

/-
  PROOF STATUS:

  ✓ normStep_eq_cbrtStep: NR step norm = cbrtStep
  ✓ normSub257Clz_eq_log2_add_two_of_pos_u256: sub/clz value = log2 + 2
  ✓ normSub257Clz_eq_cbrtSeed_of_pos_u256: sub/clz seed = cbrtSeed
  ✓ model_cbrt_eq_innerCbrt: Nat model = hand-written innerCbrt for uint256 inputs
  ✓ model_cbrt_bracket_u256_all: Nat model ∈ [m, m+1]
  ✓ model_cbrt_floor_eq_floorCbrt: Nat floor model = floorCbrt for uint256 inputs
  ✓ model_cbrt_up_eq_cbrtUpSpec: Nat cbrtUp model = cbrtUpSpec for uint256 inputs
  ✓ model_cbrt_up_evm_eq_cbrtUpSpec: EVM cbrtUp model = cbrtUpSpec
  ✓ cbrtUpSpec_upper_bound: cbrtUpSpec gives valid upper bound
  ✓ cbrtUpSpec_lower_bound: cbrtUpSpec gives tight lower bound (exact ceiling)
  ✓ model_cbrt_up_evm_upper_bound: EVM cbrtUp gives valid upper bound
  ✓ model_cbrt_up_evm_lower_bound: EVM cbrtUp gives tight lower bound
  ✓ model_cbrt_up_evm_is_ceil: EVM cbrtUp is the exact ceiling cube root (x > 0)
  ✓ model_cbrt_up_evm_is_ceil_all: EVM cbrtUp is correct for all x < 2^256 (including x = 0)
  ✓ model_cbrt_up_evm_ceil_u256: cbrtUp is the smallest integer with r³ ≥ x
  ✓ model_cbrt_evm_eq_model_cbrt: EVM model = Nat model
  ✓ model_cbrt_evm_bracket_u256_all: EVM model ∈ [m, m+1]
  ✓ model_cbrt_floor_evm_eq_floorCbrt: EVM floor = floorCbrt
  ✓ model_cbrt_floor_evm_correct: EVM floor = icbrt
-/

end CbrtYul
