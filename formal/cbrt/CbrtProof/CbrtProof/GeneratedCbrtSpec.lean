/-
  Bridge: auto-generated Lean model of Cbrt.sol ↔ proven-correct hand-written spec.

  Levels:
    1. Nat model = hand-written spec  (normStep, normSeed, model_cbrt ↔ innerCbrt)
    2. EVM model = Nat model           (no overflow on uint256)
    3. Floor correction                 (model_cbrt_floor_evm = floorCbrt = icbrt)
    4. cbrtUp rounding                  (model_cbrt_up_evm rounds up correctly)
-/
import Init
import CbrtProof.GeneratedCbrtModel
import CbrtProof.CbrtCorrect
import CbrtProof.CertifiedChain
import CbrtProof.FiniteCert
import CbrtProof.Wiring
import CbrtProof.OverflowSafety

set_option exponentiation.threshold 300

namespace CbrtGeneratedModel

open CbrtGeneratedModel
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

/-- The normalized seed expression equals cbrtSeed for positive x. -/
private theorem normSeed_eq_cbrtSeed_of_pos
    (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    normAdd (normShr 8 (normShl (normDiv (normSub 257 (normClz x)) 3) 233)) (normLt 0 x) =
      cbrtSeed x := by
  unfold normAdd normShr normShl normDiv normSub normClz normLt cbrtSeed
  simp [Nat.ne_of_gt hx, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hlog : Nat.log2 x < 256 := (Nat.log2_lt (Nat.ne_of_gt hx)).2 hx256
  have hsub : 257 - (255 - Nat.log2 x) = Nat.log2 x + 2 := by omega
  rw [hsub]
  simp [hx]

/-- model_cbrt 0 = 0 -/
private theorem model_cbrt_zero : model_cbrt 0 = 0 := by
  simp [model_cbrt, normAdd, normShr, normShl, normDiv, normSub, normClz, normLt, normMul]

/-- For positive x < 2^256, model_cbrt x = innerCbrt x. -/
theorem model_cbrt_eq_innerCbrt (x : Nat) (hx256 : x < 2 ^ 256) :
    model_cbrt x = innerCbrt x := by
  by_cases hx0 : x = 0
  · subst hx0
    simp [model_cbrt_zero, innerCbrt]
  · have hx : 0 < x := Nat.pos_of_ne_zero hx0
    have hseed : normAdd (normShr 8 (normShl (normDiv (normSub 257 (normClz x)) 3) 233)) (normLt 0 x) = cbrtSeed x :=
      normSeed_eq_cbrtSeed_of_pos x hx hx256
    unfold model_cbrt innerCbrt
    simp [Nat.ne_of_gt hx, hseed, normStep_eq_cbrtStep]

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

private theorem evmAdd_eq_normAdd_of_no_overflow
    (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) (hab : a + b < WORD_MOD) :
    evmAdd a b = normAdd a b := by
  unfold evmAdd normAdd
  simp [u256_eq_of_lt a ha, u256_eq_of_lt b hb, u256_eq_of_lt (a + b) hab]

private theorem evmLt_eq_normLt_of_u256
    (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmLt a b = normLt a b := by
  unfold evmLt normLt; simp [u256_eq_of_lt a ha, u256_eq_of_lt b hb]

private theorem evmGt_eq_normGt_of_u256
    (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmGt a b = normGt a b := by
  unfold evmGt normGt; simp [u256_eq_of_lt a ha, u256_eq_of_lt b hb]

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

private theorem zero_lt_word : (0 : Nat) < WORD_MOD := by
  unfold WORD_MOD; decide

private theorem one_lt_word : (1 : Nat) < WORD_MOD := by
  unfold WORD_MOD; decide

private theorem three_lt_word : (3 : Nat) < WORD_MOD := by
  unfold WORD_MOD; decide

private theorem evmLt_le_one (a b : Nat) : evmLt a b ≤ 1 := by
  unfold evmLt; split <;> omega

private theorem evmGt_le_one (a b : Nat) : evmGt a b ≤ 1 := by
  unfold evmGt; split <;> omega

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
private theorem seed_evm_eq_norm (x : Nat) (hx : x < WORD_MOD) :
    evmAdd (evmShr 8 (evmShl (evmDiv (evmSub 257 (evmClz x)) 3) 233)) (evmLt 0 x) =
      normAdd (normShr 8 (normShl (normDiv (normSub 257 (normClz x)) 3) 233)) (normLt 0 x) := by
  have hclz : evmClz x = normClz x := evmClz_eq_normClz_of_u256 x hx
  have hclzLe : normClz x ≤ 256 := normClz_le_256 x
  -- evmSub 257 (evmClz x) = normSub 257 (normClz x)
  have h257W : (257 : Nat) < WORD_MOD := by unfold WORD_MOD; decide
  have hclzLe257 : normClz x ≤ 257 := by omega
  have hsub : evmSub 257 (evmClz x) = normSub 257 (normClz x) := by
    simpa [hclz] using evmSub_eq_normSub_of_le 257 (normClz x) h257W hclzLe257
  have hsubLe : normSub 257 (normClz x) ≤ 257 := by unfold normSub; exact Nat.sub_le _ _
  have hsubLt : normSub 257 (normClz x) < WORD_MOD := Nat.lt_of_le_of_lt hsubLe h257W
  -- evmDiv (...) 3 = normDiv (...) 3
  have hdiv : evmDiv (evmSub 257 (evmClz x)) 3 = normDiv (normSub 257 (normClz x)) 3 := by
    simpa [hsub] using evmDiv_eq_normDiv_of_u256 (normSub 257 (normClz x)) 3 hsubLt three_lt_word
  -- q := normDiv result ≤ 85
  have hdivLe : normDiv (normSub 257 (normClz x)) 3 ≤ 85 := by
    unfold normDiv; exact Nat.le_trans (Nat.div_le_div_right hsubLe) (by decide)
  have hdivLt256 : normDiv (normSub 257 (normClz x)) 3 < 256 := by omega
  have hdivLtW : normDiv (normSub 257 (normClz x)) 3 < WORD_MOD :=
    Nat.lt_of_lt_of_le hdivLt256 (Nat.le_of_lt word_mod_gt_256)
  -- evmShl q 233: shift = q, value = 233
  -- Need: 233 * 2^q < WORD_MOD
  have h233W : (233 : Nat) < WORD_MOD := by unfold WORD_MOD; decide
  let q := normDiv (normSub 257 (normClz x)) 3
  have hqLt : q < 256 := hdivLt256
  have hshlSafe : 233 * 2 ^ q < WORD_MOD := by
    have hq_le_85 : q ≤ 85 := hdivLe
    -- 233 < 256 = 2^8, so 233 * 2^85 < 2^8 * 2^85 = 2^93 < 2^256
    have h1 : 233 * 2 ^ q ≤ 233 * 2 ^ 85 :=
      Nat.mul_le_mul_left 233 (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hq_le_85)
    have h2 : 233 * 2 ^ 85 < 2 ^ 94 := by decide
    have h3 : 2 ^ 94 < WORD_MOD := two_pow_lt_word 94 (by decide)
    omega
  have hshl : evmShl (evmDiv (evmSub 257 (evmClz x)) 3) 233 =
      normShl (normDiv (normSub 257 (normClz x)) 3) 233 := by
    rw [hdiv]
    exact evmShl_eq_normShl_of_safe q 233 hqLt h233W hshlSafe
  -- normShl result < WORD_MOD
  have hshlVal : normShl q 233 < WORD_MOD := by
    unfold normShl; rw [Nat.shiftLeft_eq]; exact hshlSafe
  -- evmShr 8 (...) = normShr 8 (...)
  have hshr : evmShr 8 (evmShl (evmDiv (evmSub 257 (evmClz x)) 3) 233) =
      normShr 8 (normShl q 233) := by
    rw [hshl]
    exact evmShr_eq_normShr_of_u256 8 (normShl q 233) (by decide) hshlVal
  -- evmLt 0 x = normLt 0 x
  have hlt : evmLt 0 x = normLt 0 x := evmLt_eq_normLt_of_u256 0 x zero_lt_word hx
  -- shr result < WORD_MOD
  have hshrLt : normShr 8 (normShl q 233) < WORD_MOD := by
    unfold normShr; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hshlVal
  -- lt result ≤ 1
  have hltLe : normLt 0 x ≤ 1 := by unfold normLt; split <;> omega
  have hltLt : normLt 0 x < WORD_MOD := Nat.lt_of_le_of_lt hltLe one_lt_word
  -- sum < WORD_MOD: shr result + lt result < shr result + 2 ≤ 2^86 + 2 < WORD_MOD
  have hshr_bound : normShr 8 (normShl q 233) < 2 ^ 86 := by
    unfold normShr normShl
    rw [Nat.shiftLeft_eq]
    -- 233 * 2^q / 2^8 ≤ 233 * 2^85 / 256 < 2^86
    have h1 : 233 * 2 ^ q / 2 ^ 8 ≤ 233 * 2 ^ 85 / 2 ^ 8 :=
      Nat.div_le_div_right (Nat.mul_le_mul_left 233
        (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hdivLe))
    have h2 : 233 * 2 ^ 85 / 2 ^ 8 < 2 ^ 86 := by decide
    omega
  have hsum : normShr 8 (normShl q 233) + normLt 0 x < WORD_MOD := by
    have h86 : 2 ^ 86 + 1 < WORD_MOD := by unfold WORD_MOD; decide
    omega
  rw [hshr, hlt]
  exact evmAdd_eq_normAdd_of_no_overflow
    (normShr 8 (normShl q 233)) (normLt 0 x) hshrLt hltLt
    (by simpa [normAdd] using hsum)

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
-- Small x: model_cbrt_evm = model_cbrt for all x < 256.
private theorem small_cbrt_evm_eq : ∀ v : Fin 256,
    model_cbrt_evm v.val = model_cbrt v.val := by decide

theorem model_cbrt_evm_eq_model_cbrt
    (x : Nat)
    (hx256 : x < WORD_MOD) :
    model_cbrt_evm x = model_cbrt x := by
  by_cases hx0 : x = 0
  · subst hx0; decide
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
        · have hlog := (Nat.log2_eq_iff (Nat.ne_of_gt hx)).1 rfl
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
        exact (Nat.log2_eq_iff (Nat.ne_of_gt hx)).1 rfl
      -- Seed and interval
      have hseedOf : cbrtSeed x = seedOf idx := CbrtWiring.cbrtSeed_eq_certSeed idx x hOct
      have hinterval := CbrtWiring.m_within_cert_interval idx x m hmlo hmhi hOct
      -- Define z0..z6
      let z0 := seedOf idx
      let z1 := cbrtStep x z0
      let z2 := cbrtStep x z1
      let z3 := cbrtStep x z2
      let z4 := cbrtStep x z3
      let z5 := cbrtStep x z4
      let z6 := cbrtStep x z5
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
      have hmz5 : m ≤ z5 := by
        dsimp [z5]; exact cbrt_step_floor_bound x z4 m hz4Pos hmlo
      have hz5Pos : 0 < z5 := Nat.lt_of_lt_of_le hm hmz5
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
      have hd5 : z5 - m ≤ d5Of idx := by
        have h := CbrtCertified.step_from_bound x m (loOf idx) z4 (d4Of idx) hm2 hloPos
          hinterval.1 hmhi hmz4 hd4 h2d4
        show cbrtStep x z4 - m ≤ d5Of idx; unfold d5Of; exact h
      have h2d5 : 2 * d5Of idx ≤ m := Nat.le_trans (two_d5_le_lo idx) hinterval.1
      -- Upper bounds: z_k ≤ 2m (from error ≤ d_k ≤ lo/2 ≤ m/2, so z_k ≤ m + m/2 < 2m)
      -- Actually: 2*d_k ≤ lo ≤ m, so d_k ≤ m/2, so z_k ≤ m + d_k ≤ m + m = 2m
      have hd1m : d1Of idx ≤ m := by omega
      have hd2m : d2Of idx ≤ m := by omega
      have hd3m : d3Of idx ≤ m := by omega
      have hd4m : d4Of idx ≤ m := by omega
      have hd5m : d5Of idx ≤ m := by omega
      have hz1_le_2m : z1 ≤ 2 * m := by omega
      have hz2_le_2m : z2 ≤ 2 * m := by omega
      have hz3_le_2m : z3 ≤ 2 * m := by omega
      have hz4_le_2m : z4 ≤ 2 * m := by omega
      have hz5_le_2m : z5 ≤ 2 * m := by omega
      -- z_k < 2^87 (from z_k ≤ 2m < 2^87)
      have hz1_87 : z1 < 2 ^ 87 := by omega
      have hz2_87 : z2 < 2 ^ 87 := by omega
      have hz3_87 : z3 < 2 ^ 87 := by omega
      have hz4_87 : z4 < 2 ^ 87 := by omega
      have hz5_87 : z5 < 2 ^ 87 := by omega
      -- z_k * z_k < WORD_MOD (from z_k < 2^87)
      have hzz1 : z1 * z1 < WORD_MOD := zsq_lt_word_of_lt_87 z1 hz1_87
      have hzz2 : z2 * z2 < WORD_MOD := zsq_lt_word_of_lt_87 z2 hz2_87
      have hzz3 : z3 * z3 < WORD_MOD := zsq_lt_word_of_lt_87 z3 hz3_87
      have hzz4 : z4 * z4 < WORD_MOD := zsq_lt_word_of_lt_87 z4 hz4_87
      have hzz5 : z5 * z5 < WORD_MOD := zsq_lt_word_of_lt_87 z5 hz5_87
      -- x/(z_k*z_k) + 2*z_k < WORD_MOD (from cbrt_sum_lt_word_of_bounds)
      have hsum1 : x / (z1 * z1) + 2 * z1 < WORD_MOD :=
        cbrt_sum_lt_word_of_bounds x m z1 hx256 hm hmlo hmhi hmz1 hz1_le_2m
      have hsum2 : x / (z2 * z2) + 2 * z2 < WORD_MOD :=
        cbrt_sum_lt_word_of_bounds x m z2 hx256 hm hmlo hmhi hmz2 hz2_le_2m
      have hsum3 : x / (z3 * z3) + 2 * z3 < WORD_MOD :=
        cbrt_sum_lt_word_of_bounds x m z3 hx256 hm hmlo hmhi hmz3 hz3_le_2m
      have hsum4 : x / (z4 * z4) + 2 * z4 < WORD_MOD :=
        cbrt_sum_lt_word_of_bounds x m z4 hx256 hm hmlo hmhi hmz4 hz4_le_2m
      have hsum5 : x / (z5 * z5) + 2 * z5 < WORD_MOD :=
        cbrt_sum_lt_word_of_bounds x m z5 hx256 hm hmlo hmhi hmz5 hz5_le_2m
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
      have hz5W : z5 < WORD_MOD := Nat.lt_of_lt_of_le hz5_87 (Nat.le_of_lt (two_pow_lt_word 87 (by decide)))
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
      have hstep6 : evmDiv (evmAdd (evmAdd (evmDiv x (evmMul z5 z5)) z5) z5) 3 = z6 := by
        have h := step_evm_eq_norm_of_safe x z5 hx256 hz5Pos hz5W hzz5 hsum5
        simpa [z6, normStep_eq_cbrtStep] using h
      -- Seed: EVM = norm
      have hseedNorm :
          normAdd (normShr 8 (normShl (normDiv (normSub 257 (normClz x)) 3) 233)) (normLt 0 x) =
            seedOf idx := by
        exact (normSeed_eq_cbrtSeed_of_pos x hx hx256).trans hseedOf
      have hseedEvm :
          evmAdd (evmShr 8 (evmShl (evmDiv (evmSub 257 (evmClz x)) 3) 233)) (evmLt 0 x) =
            seedOf idx := by
        exact (seed_evm_eq_norm x hx256).trans hseedNorm
      -- Final assembly
      have hxmod : u256 x = x := u256_eq_of_lt x hx256
      unfold model_cbrt_evm model_cbrt
      simp [hxmod, hseedEvm, hseedNorm, z0, z1, z2, z3, z4, z5, z6,
        hstep1, hstep2, hstep3, hstep4, hstep5, hstep6, normStep_eq_cbrtStep]

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
      (if z = 0 then 0 else if x / (z * z) < z then z - 1 else z) := by
  by_cases hz0 : z = 0
  · subst hz0; simp [normSub, normLt, normDiv, normMul]
  · by_cases hlt : x / (z * z) < z
    · simp [normSub, normLt, normDiv, normMul, hz0, hlt]
    · simp [normSub, normLt, normDiv, normMul, hz0, hlt]

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
  · subst hx0; decide
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
-- Trivial with the new model: z * (z * z) = z * z * z by associativity,
-- so normLt(normMul z (normMul z z), x) = if z*z*z < x then 1 else 0.
private theorem model_cbrt_up_norm_eq_cbrtUpSpec
    (x : Nat) (_hx : 0 < x) (hx256 : x < 2 ^ 256) :
    model_cbrt_up x = cbrtUpSpec x := by
  have hinner : model_cbrt x = innerCbrt x := model_cbrt_eq_innerCbrt x hx256
  unfold model_cbrt_up cbrtUpSpec
  simp only [hinner, normAdd, normLt, normMul, Nat.mul_assoc]
  -- Both sides now have z*(z*z). Just need: z + (if _ then 1 else 0) = if _ then z+1 else z
  split <;> simp_all

theorem model_cbrt_up_eq_cbrtUpSpec
    (x : Nat) (hx : 0 < x) (hx256 : x < 2 ^ 256) :
    model_cbrt_up x = cbrtUpSpec x :=
  model_cbrt_up_norm_eq_cbrtUpSpec x hx hx256

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
    model_cbrt_up_norm_eq_cbrtUpSpec x hx hx256
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
-- Summary
-- ============================================================================

/-
  PROOF STATUS:

  ✓ normStep_eq_cbrtStep: NR step norm = cbrtStep
  ✓ normSeed_eq_cbrtSeed_of_pos: norm seed = cbrtSeed
  ✓ model_cbrt_eq_innerCbrt: Nat model = hand-written innerCbrt
  ✓ model_cbrt_bracket_u256_all: Nat model ∈ [m, m+1]
  ✓ model_cbrt_floor_eq_floorCbrt: Nat floor model = floorCbrt
  ✓ model_cbrt_up_eq_cbrtUpSpec: Nat cbrtUp model = cbrtUpSpec
  ✓ model_cbrt_up_evm_eq_cbrtUpSpec: EVM cbrtUp model = cbrtUpSpec
  ✓ cbrtUpSpec_upper_bound: cbrtUpSpec gives valid upper bound
  ✓ cbrtUpSpec_lower_bound: cbrtUpSpec gives tight lower bound (exact ceiling)
  ✓ model_cbrt_up_evm_upper_bound: EVM cbrtUp gives valid upper bound
  ✓ model_cbrt_up_evm_lower_bound: EVM cbrtUp gives tight lower bound
  ✓ model_cbrt_up_evm_is_ceil: EVM cbrtUp is the exact ceiling cube root (x > 0)
  ✓ model_cbrt_up_evm_is_ceil_all: EVM cbrtUp is correct for all x < 2^256 (including x = 0)
  ✓ model_cbrt_evm_eq_model_cbrt: EVM model = Nat model
  ✓ model_cbrt_evm_bracket_u256_all: EVM model ∈ [m, m+1]
  ✓ model_cbrt_floor_evm_eq_floorCbrt: EVM floor = floorCbrt
  ✓ model_cbrt_floor_evm_correct: EVM floor = icbrt
-/

end CbrtGeneratedModel
