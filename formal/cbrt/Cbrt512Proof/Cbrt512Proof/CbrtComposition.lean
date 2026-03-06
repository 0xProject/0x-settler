/-
  Composition: the full 512-bit cbrt algorithm gives icbrt(x_norm) ± 1.

  After:
    1. BaseCase: r_hi = icbrt(w), res = w - r_hi³, d = 3*r_hi²
       where w = x_hi_1 / 4
    2. Extract limb_hi (next 86 bits of x_norm)
    3. KaratsubaQuotient: r_lo = (res * 2^86 + limb_hi) / d
    4. QuadraticCorrection: r_qc = r_hi * 2^86 + r_lo - r_lo²/(r_hi * 2^86)

  We prove: icbrt(x_norm) ≤ r_qc ≤ icbrt(x_norm) + 1
  where x_norm = x_hi_1 * 2^256 + x_lo_1.

  The key algebraic insight: with R = r_hi * 2^86:
    - The Karatsuba quotient captures the linear term: r_lo ≈ (x_norm - R³) / (3R²)
    - The quadratic correction subtracts r_lo²/R ≈ (x_norm-R³)² / (9R⁵)
    - The remaining cubic error r_lo³/(3R²) < 2^258/(3·2^338) < 1
-/
import Cbrt512Proof.GeneratedCbrt512Model
import Cbrt512Proof.CbrtBaseCase
import Cbrt512Proof.CbrtKaratsubaQuotient
import Cbrt512Proof.CbrtAlgebraic
import Cbrt512Proof.EvmBridge
import CbrtProof.CbrtCorrect

namespace Cbrt512Spec

open Cbrt512GeneratedModel

-- ============================================================================
-- QC helper lemmas
-- ============================================================================

/-- The constant expression evmAnd(evmAnd(86,255),255) evaluates to 86. -/
private theorem qc_const_86 : evmAnd (evmAnd 86 255) 255 = 86 := by
  unfold evmAnd u256 WORD_MOD; native_decide

/-- Bitwise OR of two values ≤ 1 is ≤ 1. -/
private theorem or_le_one (a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) : a ||| b ≤ 1 := by
  have : a = 0 ∨ a = 1 := by omega
  have : b = 0 ∨ b = 1 := by omega
  rcases ‹a = 0 ∨ a = 1› with rfl | rfl <;> rcases ‹b = 0 ∨ b = 1› with rfl | rfl <;> decide

/-- evmLt returns a value ≤ 1. -/
private theorem evmLt_le_one (a b : Nat) : evmLt a b ≤ 1 := by
  unfold evmLt; split <;> omega

/-- evmEq returns a value ≤ 1. -/
private theorem evmEq_le_one (a b : Nat) : evmEq a b ≤ 1 := by
  unfold evmEq; split <;> omega

/-- Bitwise AND of two values ≤ 1 is ≤ 1. -/
private theorem and_le_one (a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) : a &&& b ≤ 1 := by
  have : a = 0 ∨ a = 1 := by omega
  have : b = 0 ∨ b = 1 := by omega
  rcases ‹a = 0 ∨ a = 1› with rfl | rfl <;> rcases ‹b = 0 ∨ b = 1› with rfl | rfl <;> decide

/-- evmAnd of values ≤ 1 is ≤ 1. -/
private theorem evmAnd_le_one (a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) :
    evmAnd a b ≤ 1 := by
  unfold evmAnd u256 WORD_MOD
  have ha' : a % 2 ^ 256 = a := Nat.mod_eq_of_lt (by omega)
  have hb' : b % 2 ^ 256 = b := Nat.mod_eq_of_lt (by omega)
  simp only [ha', hb']
  exact and_le_one a b ha hb

/-- evmOr of values ≤ 1 is ≤ 1. -/
private theorem evmOr_le_one (a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) :
    evmOr a b ≤ 1 := by
  unfold evmOr u256 WORD_MOD
  have ha' : a % 2 ^ 256 = a := Nat.mod_eq_of_lt (by omega)
  have hb' : b % 2 ^ 256 = b := Nat.mod_eq_of_lt (by omega)
  simp only [ha', hb']
  exact or_le_one a b ha hb

/-- The undershoot check in the QC produces a value ≤ 1. -/
private theorem qc_undershoot_le_one (eps3 rem r_hi : Nat) :
    evmOr
      (evmLt (evmShr (evmAnd (evmAnd 86 255) 255) eps3)
             (evmShr (evmAnd (evmAnd 86 255) 255) rem))
      (evmAnd
        (evmEq (evmShr (evmAnd (evmAnd 86 255) 255) eps3)
               (evmShr (evmAnd (evmAnd 86 255) 255) rem))
        (evmLt (evmMul (evmAnd eps3 77371252455336267181195263) r_hi)
               (evmShl (evmAnd (evmAnd 86 255) 255)
                       (evmAnd rem 77371252455336267181195263)))) ≤ 1 :=
  evmOr_le_one _ _
    (evmLt_le_one _ _)
    (evmAnd_le_one _ _
      (evmEq_le_one _ _)
      (evmLt_le_one _ _))

-- ============================================================================
-- Quadratic correction EVM bridge
-- ============================================================================

/-- The quadratic correction with undershoot prevention.
    r = r_hi * 2^86 + r_lo - c + undershoot
    where c = r_lo²/(r_hi * 2^86) and undershoot ∈ {0, 1}.
    The undershoot check adds 1 when the Karatsuba remainder `rem` indicates
    the correction over-subtracted.

    For the Nat-level composition, the result ≥ R + r_lo - c (the old formula),
    ensuring the algorithm never returns less than icbrt(x_norm). -/
theorem model_cbrtQuadraticCorrection_evm_correct
    (r_hi r_lo rem : Nat)
    (hr_hi : r_hi < WORD_MOD) (hr_lo : r_lo < WORD_MOD) (hrem : rem < WORD_MOD)
    (hr_hi_pos : 2 ≤ r_hi)
    (hr_hi_bound : r_hi < 2 ^ 85)
    (hr_lo_bound : r_lo < 2 ^ 87) :
    let R := r_hi * 2 ^ 86
    let correction := r_lo * r_lo / R
    R + r_lo - correction ≤ model_cbrtQuadraticCorrection_evm r_hi r_lo rem ∧
    model_cbrtQuadraticCorrection_evm r_hi r_lo rem ≤ R + r_lo - correction + 1 ∧
    model_cbrtQuadraticCorrection_evm r_hi r_lo rem < WORD_MOD := by
  simp only
  -- ======== Bounds setup ========
  have hR_ge : 2 ^ 87 ≤ r_hi * 2 ^ 86 :=
    calc 2 ^ 87 = 2 * 2 ^ 86 := by
          rw [show (87 : Nat) = 1 + 86 from rfl, Nat.pow_add]
      _ ≤ r_hi * 2 ^ 86 := Nat.mul_le_mul_right _ hr_hi_pos
  have hR_lt : r_hi * 2 ^ 86 < 2 ^ 171 :=
    calc r_hi * 2 ^ 86
        < 2 ^ 85 * 2 ^ 86 := Nat.mul_lt_mul_of_pos_right hr_hi_bound (Nat.two_pow_pos 86)
      _ = 2 ^ 171 := by rw [← Nat.pow_add]
  have hR_wm : r_hi * 2 ^ 86 < WORD_MOD := by unfold WORD_MOD; omega
  have hR_pos : 0 < r_hi * 2 ^ 86 := by omega
  have hr_lo_sq : r_lo * r_lo < 2 ^ 174 := by
    cases Nat.eq_or_lt_of_le (Nat.zero_le r_lo) with
    | inl h => rw [← h]; simp
    | inr h =>
      calc r_lo * r_lo
          < r_lo * 2 ^ 87 := Nat.mul_lt_mul_of_pos_left hr_lo_bound h
        _ ≤ 2 ^ 87 * 2 ^ 87 := Nat.mul_le_mul_right _ (Nat.le_of_lt hr_lo_bound)
        _ = 2 ^ 174 := by rw [← Nat.pow_add]
  have hr_lo_sq_wm : r_lo * r_lo < WORD_MOD := by unfold WORD_MOD; omega
  have hR_gt_rlo : r_lo < r_hi * 2 ^ 86 := by omega
  have hc_le : r_lo * r_lo / (r_hi * 2 ^ 86) ≤ r_lo := by
    cases Nat.eq_or_lt_of_le (Nat.zero_le r_lo) with
    | inl h => rw [← h]; simp
    | inr h =>
      exact Nat.le_of_lt ((Nat.div_lt_iff_lt_mul hR_pos).mpr
        (Nat.mul_lt_mul_of_pos_left hR_gt_rlo h))
  have hcR_le : (r_lo * r_lo / (r_hi * 2 ^ 86)) * (r_hi * 2 ^ 86) ≤ r_lo * r_lo :=
    Nat.div_mul_le_self _ _
  have hc_wm : r_lo * r_lo / (r_hi * 2 ^ 86) < WORD_MOD :=
    Nat.lt_of_le_of_lt hc_le hr_lo
  have hcR_wm : (r_lo * r_lo / (r_hi * 2 ^ 86)) * (r_hi * 2 ^ 86) < WORD_MOD :=
    Nat.lt_of_le_of_lt hcR_le hr_lo_sq_wm
  -- ======== EVM-to-Nat reduction lemmas ========
  let c := r_lo * r_lo / (r_hi * 2 ^ 86)
  have hR_eq : evmShl (evmAnd (evmAnd 86 255) 255) r_hi = r_hi * 2 ^ 86 := by
    rw [qc_const_86, evmShl_eq' 86 r_hi (by omega) hr_hi]
    exact Nat.mod_eq_of_lt hR_wm
  have hSq_eq : evmMul r_lo r_lo = r_lo * r_lo := by
    rw [evmMul_eq' r_lo r_lo hr_lo hr_lo]; exact Nat.mod_eq_of_lt hr_lo_sq_wm
  have hC_eq : evmDiv (r_lo * r_lo) (r_hi * 2 ^ 86) = c :=
    evmDiv_eq' _ _ hr_lo_sq_wm hR_pos hR_wm
  have hCR_eq : evmMul c (r_hi * 2 ^ 86) = c * (r_hi * 2 ^ 86) := by
    rw [evmMul_eq' c _ hc_wm hR_wm]; exact Nat.mod_eq_of_lt hcR_wm
  have hResid_eq : evmSub (r_lo * r_lo) (c * (r_hi * 2 ^ 86)) =
      r_lo * r_lo % (r_hi * 2 ^ 86) := by
    rw [evmSub_eq_of_le _ _ hr_lo_sq_wm hcR_le,
        show c * (r_hi * 2 ^ 86) = (r_hi * 2 ^ 86) * c from Nat.mul_comm _ _]
    -- Goal: r_lo*r_lo - R*c = r_lo*r_lo % R  where c = r_lo*r_lo / R
    -- From div_add_mod: R * c + r_lo*r_lo % R = r_lo*r_lo
    have hdm := Nat.div_add_mod (r_lo * r_lo) (r_hi * 2 ^ 86)
    -- hdm : R * (r_lo*r_lo / R) + r_lo*r_lo % R = r_lo*r_lo
    -- But c is let-bound to r_lo*r_lo / R, so R * c = R * (r_lo*r_lo / R)
    -- rw [Nat.add_comm] at hdm gives: r_lo*r_lo % R + R * c = r_lo*r_lo
    rw [Nat.add_comm] at hdm
    exact Nat.sub_eq_of_eq_add hdm.symm
  have hmod_lt : r_lo * r_lo % (r_hi * 2 ^ 86) < WORD_MOD :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hR_pos) (by unfold WORD_MOD; omega)
  have heps3_wm : (r_lo * r_lo % (r_hi * 2 ^ 86)) * 3 < WORD_MOD := by
    calc (r_lo * r_lo % (r_hi * 2 ^ 86)) * 3
        < (r_hi * 2 ^ 86) * 3 := Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ hR_pos) (by omega)
      _ < 2 ^ 171 * 3 := Nat.mul_lt_mul_of_pos_right hR_lt (by omega)
      _ < WORD_MOD := by unfold WORD_MOD; omega
  have hEps3_eq : evmMul (r_lo * r_lo % (r_hi * 2 ^ 86)) 3 =
      (r_lo * r_lo % (r_hi * 2 ^ 86)) * 3 := by
    rw [evmMul_eq' _ 3 hmod_lt (by unfold WORD_MOD; omega)]
    exact Nat.mod_eq_of_lt heps3_wm
  have hSub_eq : evmSub r_lo c = r_lo - c :=
    evmSub_eq_of_le _ _ hr_lo hc_le
  have hGt_eq : evmGt c 1 = if c > 1 then 1 else 0 :=
    evmGt_eq' c 1 hc_wm (by unfold WORD_MOD; omega)
  -- ======== Unfold model and simplify (following base case pattern) ========
  unfold model_cbrtQuadraticCorrection_evm
  simp only [u256_id' r_hi hr_hi, u256_id' r_lo hr_lo, u256_id' rem hrem,
             hR_eq, hSq_eq, hC_eq, hCR_eq, hResid_eq, hEps3_eq, hSub_eq, hGt_eq]
  -- ======== Case split on c > 1 ========
  by_cases hcgt : c > 1
  · -- Case c > 1: undershoot fires, result = R + (r_lo - c) + u where u ≤ 1
    rw [if_pos hcgt, if_pos (show (1 : Nat) ≠ 0 from by omega)]
    -- The undershoot check ≤ 1
    have h_us_le := qc_undershoot_le_one
        ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) rem r_hi
    -- Abstract over the undershoot value
    generalize evmOr _ _ = us at h_us_le ⊢
    -- evmAdd simplifications
    have h_rloc_wm : r_lo - c < WORD_MOD := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hr_lo
    have h_us_wm : us < WORD_MOD := by unfold WORD_MOD; omega
    have h_inner : r_lo - c + us < WORD_MOD := by unfold WORD_MOD; omega
    rw [evmAdd_eq' _ _ h_rloc_wm h_us_wm h_inner,
        evmAdd_eq' _ _ hR_wm h_inner (by unfold WORD_MOD; omega)]
    refine ⟨by omega, by omega, by unfold WORD_MOD; omega⟩
  · -- Case c ≤ 1: no undershoot, result = R + (r_lo - c)
    rw [if_neg hcgt, if_neg (fun h : (0 : Nat) ≠ 0 => h rfl)]
    have h_rloc_wm : r_lo - c < WORD_MOD := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hr_lo
    rw [evmAdd_eq' _ _ hR_wm h_rloc_wm (by unfold WORD_MOD; omega)]
    refine ⟨by omega, by omega, by unfold WORD_MOD; omega⟩

/-- When c ≤ 1, the QC returns exactly r_qc (no undershoot correction). -/
theorem model_cbrtQuadraticCorrection_evm_exact_when_c_le1
    (r_hi r_lo rem : Nat)
    (hr_hi : r_hi < WORD_MOD) (hr_lo : r_lo < WORD_MOD) (hrem : rem < WORD_MOD)
    (hr_hi_pos : 2 ≤ r_hi)
    (hr_hi_bound : r_hi < 2 ^ 85)
    (hr_lo_bound : r_lo < 2 ^ 87)
    (hc_le1 : r_lo * r_lo / (r_hi * 2 ^ 86) ≤ 1) :
    model_cbrtQuadraticCorrection_evm r_hi r_lo rem =
      r_hi * 2 ^ 86 + r_lo - r_lo * r_lo / (r_hi * 2 ^ 86) := by
  -- Reuse all the EVM simplification from the main bridge proof
  have hR_ge : 2 ^ 87 ≤ r_hi * 2 ^ 86 :=
    calc 2 ^ 87 = 2 * 2 ^ 86 := by
          rw [show (87 : Nat) = 1 + 86 from rfl, Nat.pow_add]
      _ ≤ r_hi * 2 ^ 86 := Nat.mul_le_mul_right _ hr_hi_pos
  have hR_lt : r_hi * 2 ^ 86 < 2 ^ 171 :=
    calc r_hi * 2 ^ 86
        < 2 ^ 85 * 2 ^ 86 := Nat.mul_lt_mul_of_pos_right hr_hi_bound (Nat.two_pow_pos 86)
      _ = 2 ^ 171 := by rw [← Nat.pow_add]
  have hR_wm : r_hi * 2 ^ 86 < WORD_MOD := by unfold WORD_MOD; omega
  have hR_pos : 0 < r_hi * 2 ^ 86 := by omega
  have hr_lo_sq_wm : r_lo * r_lo < WORD_MOD := by
    cases Nat.eq_or_lt_of_le (Nat.zero_le r_lo) with
    | inl h => rw [← h]; simp; unfold WORD_MOD; omega
    | inr h =>
      calc r_lo * r_lo
          < r_lo * 2 ^ 87 := Nat.mul_lt_mul_of_pos_left hr_lo_bound h
        _ ≤ 2 ^ 87 * 2 ^ 87 := Nat.mul_le_mul_right _ (Nat.le_of_lt hr_lo_bound)
        _ = 2 ^ 174 := by rw [← Nat.pow_add]
      unfold WORD_MOD; omega
  have hc_le : r_lo * r_lo / (r_hi * 2 ^ 86) ≤ r_lo := by
    cases Nat.eq_or_lt_of_le (Nat.zero_le r_lo) with
    | inl h => rw [← h]; simp
    | inr h =>
      exact Nat.le_of_lt ((Nat.div_lt_iff_lt_mul hR_pos).mpr
        (Nat.mul_lt_mul_of_pos_left (by omega : r_hi * 2 ^ 86 > r_lo) h))
  let c := r_lo * r_lo / (r_hi * 2 ^ 86)
  have hc_wm : c < WORD_MOD := Nat.lt_of_le_of_lt hc_le hr_lo
  have hcR_le : c * (r_hi * 2 ^ 86) ≤ r_lo * r_lo := Nat.div_mul_le_self _ _
  have hcR_wm : c * (r_hi * 2 ^ 86) < WORD_MOD :=
    Nat.lt_of_le_of_lt hcR_le hr_lo_sq_wm
  -- EVM simplifications
  have hR_eq : evmShl (evmAnd (evmAnd 86 255) 255) r_hi = r_hi * 2 ^ 86 := by
    rw [qc_const_86, evmShl_eq' 86 r_hi (by omega) hr_hi]
    exact Nat.mod_eq_of_lt hR_wm
  have hSq_eq : evmMul r_lo r_lo = r_lo * r_lo := by
    rw [evmMul_eq' r_lo r_lo hr_lo hr_lo]; exact Nat.mod_eq_of_lt hr_lo_sq_wm
  have hC_eq : evmDiv (r_lo * r_lo) (r_hi * 2 ^ 86) = c :=
    evmDiv_eq' _ _ hr_lo_sq_wm hR_pos hR_wm
  have hCR_eq : evmMul c (r_hi * 2 ^ 86) = c * (r_hi * 2 ^ 86) := by
    rw [evmMul_eq' c _ hc_wm hR_wm]; exact Nat.mod_eq_of_lt hcR_wm
  have hResid_eq : evmSub (r_lo * r_lo) (c * (r_hi * 2 ^ 86)) =
      r_lo * r_lo % (r_hi * 2 ^ 86) := by
    rw [evmSub_eq_of_le _ _ hr_lo_sq_wm hcR_le,
        show c * (r_hi * 2 ^ 86) = (r_hi * 2 ^ 86) * c from Nat.mul_comm _ _]
    have hdm := Nat.div_add_mod (r_lo * r_lo) (r_hi * 2 ^ 86)
    rw [Nat.add_comm] at hdm
    exact Nat.sub_eq_of_eq_add hdm.symm
  have hmod_lt : r_lo * r_lo % (r_hi * 2 ^ 86) < WORD_MOD :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hR_pos) (by unfold WORD_MOD; omega)
  have heps3_wm : (r_lo * r_lo % (r_hi * 2 ^ 86)) * 3 < WORD_MOD := by
    calc (r_lo * r_lo % (r_hi * 2 ^ 86)) * 3
        < (r_hi * 2 ^ 86) * 3 := Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ hR_pos) (by omega)
      _ < 2 ^ 171 * 3 := Nat.mul_lt_mul_of_pos_right hR_lt (by omega)
      _ < WORD_MOD := by unfold WORD_MOD; omega
  have hEps3_eq : evmMul (r_lo * r_lo % (r_hi * 2 ^ 86)) 3 =
      (r_lo * r_lo % (r_hi * 2 ^ 86)) * 3 := by
    rw [evmMul_eq' _ 3 hmod_lt (by unfold WORD_MOD; omega)]
    exact Nat.mod_eq_of_lt heps3_wm
  have hSub_eq : evmSub r_lo c = r_lo - c :=
    evmSub_eq_of_le _ _ hr_lo hc_le
  have hGt_eq : evmGt c 1 = if c > 1 then 1 else 0 :=
    evmGt_eq' c 1 hc_wm (by unfold WORD_MOD; omega)
  -- Unfold and simplify
  unfold model_cbrtQuadraticCorrection_evm
  simp only [u256_id' r_hi hr_hi, u256_id' r_lo hr_lo, u256_id' rem hrem,
             hR_eq, hSq_eq, hC_eq, hCR_eq, hResid_eq, hEps3_eq, hSub_eq, hGt_eq]
  -- c ≤ 1: the if-branch is NOT taken
  rw [if_neg (by omega : ¬(c > 1)), if_neg (fun h : (0 : Nat) ≠ 0 => h rfl)]
  have h_rloc_wm : r_lo - c < WORD_MOD := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hr_lo
  rw [evmAdd_eq' _ _ hR_wm h_rloc_wm (by unfold WORD_MOD; omega)]
  -- Goal: r_hi * 2^86 + (r_lo - c) = r_hi * 2^86 + r_lo - c
  -- In Nat: a + (b - c) = a + b - c when c ≤ b
  omega

-- qc_undershoot_cube_lt is defined after sub-lemmas A, B, E1, E2 below.

-- ============================================================================
-- P2 helper (c ≤ 1): (r_qc + 1)³ > x_norm, hence icbrt ≤ r_qc
-- ============================================================================

set_option exponentiation.threshold 1024 in
/-- When c ≤ 1, the cube of (r_qc + 1) exceeds x_norm.
    Key: x_norm < R³ + 3R²·(r_lo+1) (tight upper bound from rem < 3m², c_tail < 2^172).
    And (r_qc+1)³ = (R+s)³ where s = r_lo-c+1, with 3Rs² + s³ ≥ 3R²c when c ≤ 1.
    For c=0: trivial (3Rs² ≥ 0 ≥ 0). For c=1: r_lo² ≥ R, so 3Rr_lo² ≥ 3R². -/
theorem r_qc_succ1_cube_gt_when_c_le1 (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD)
    (hc_le1 : let m := icbrt (x_hi_1 / 4)
              let d := 3 * (m * m)
              let res := x_hi_1 / 4 - m * m * m
              let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
              let r_lo := (res * 2 ^ 86 + limb_hi) / d
              r_lo * r_lo / (m * 2 ^ 86) ≤ 1) :
    let w := x_hi_1 / 4
    let m := icbrt w
    let res := w - m * m * m
    let d := 3 * (m * m)
    let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
    let r_lo := (res * 2 ^ 86 + limb_hi) / d
    let R := m * 2 ^ 86
    let correction := r_lo * r_lo / R
    let r_qc := R + r_lo - correction
    let x_norm := x_hi_1 * 2 ^ 256 + x_lo_1
    x_norm < (r_qc + 1) * (r_qc + 1) * (r_qc + 1) := by
  simp only
  -- ======== Step 1: Base case properties ========
  have hbc := model_cbrtBaseCase_evm_correct x_hi_1 hxhi_lo hxhi_hi
  have hm_lo : 2 ^ 83 ≤ icbrt (x_hi_1 / 4) := hbc.2.2.2.1
  have hm_hi : icbrt (x_hi_1 / 4) < 2 ^ 85 := hbc.2.2.2.2.1
  have hcube_le_w : icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)
      ≤ x_hi_1 / 4 := hbc.2.2.2.2.2.1
  have hres_bound : x_hi_1 / 4 - icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)
      ≤ 3 * (icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)) + 3 * icbrt (x_hi_1 / 4) :=
    hbc.2.2.2.2.2.2.1
  have hd_pos : 3 * (icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)) > 0 :=
    hbc.2.2.2.2.2.2.2.2.2.2
  -- Abbreviate
  let m := icbrt (x_hi_1 / 4)
  let w := x_hi_1 / 4
  let res := w - m * m * m
  let d := 3 * (m * m)
  let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
  let r_lo := (res * 2 ^ 86 + limb_hi) / d
  let R := m * 2 ^ 86
  let c := r_lo * r_lo / R
  let rem_kq := (res * 2 ^ 86 + limb_hi) % d
  let c_tail := x_lo_1 % 2 ^ 172
  -- ======== Step 2: Key bounds ========
  have hR_lo : 2 ^ 169 ≤ R :=
    calc 2 ^ 169 = 2 ^ 83 * 2 ^ 86 := by rw [← Nat.pow_add]
      _ ≤ m * 2 ^ 86 := Nat.mul_le_mul_right _ hm_lo
  have hR_pos : 0 < R := by omega
  have hlimb_bound : limb_hi < 2 ^ 86 := by
    show (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86
    have hmod4 : x_hi_1 % 4 < 4 := Nat.mod_lt _ (by omega)
    have hdiv : x_lo_1 / 2 ^ 172 < 2 ^ 84 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 172)]
      calc x_lo_1 < WORD_MOD := hxlo
        _ = 2 ^ 84 * 2 ^ 172 := by unfold WORD_MOD; rw [← Nat.pow_add]
    have : (x_hi_1 % 4) * 2 ^ 84 < 2 ^ 86 :=
      calc (x_hi_1 % 4) * 2 ^ 84 < 4 * 2 ^ 84 :=
              Nat.mul_lt_mul_of_pos_right hmod4 (Nat.two_pow_pos 84)
        _ = 2 ^ 86 := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
    omega
  have hr_lo_bound : r_lo < 2 ^ 87 := by
    show (res * 2 ^ 86 + limb_hi) / d < 2 ^ 87
    rw [Nat.div_lt_iff_lt_mul hd_pos]
    have h2m : 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
    calc res * 2 ^ 86 + limb_hi
        < (res + 1) * 2 ^ 86 := by omega
      _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by
          apply Nat.mul_le_mul_right; exact Nat.succ_le_succ hres_bound
      _ ≤ (2 * (3 * (m * m))) * 2 ^ 86 := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ 87 * (3 * (m * m)) := by
          rw [show (2 : Nat) ^ 87 = 2 * 2 ^ 86 from by
            rw [show (87 : Nat) = 1 + 86 from rfl, Nat.pow_add]]; omega
  -- c ≤ r_lo
  have hc_le : c ≤ r_lo := by
    show r_lo * r_lo / R ≤ r_lo
    cases Nat.eq_or_lt_of_le (Nat.zero_le r_lo) with
    | inl h => rw [← h]; simp
    | inr h =>
      exact Nat.le_of_lt ((Nat.div_lt_iff_lt_mul hR_pos).mpr
        (Nat.mul_lt_mul_of_pos_left (by omega : r_lo < R) h))
  -- rem_kq < d
  have hrem_lt : rem_kq < d := Nat.mod_lt _ hd_pos
  -- c_tail < 2^172
  have hctail_lt : c_tail < 2 ^ 172 := Nat.mod_lt _ (Nat.two_pow_pos 172)
  -- ======== Step 3: Tight x_norm upper bound ========
  -- x_norm = m³·2^258 + (d·r_lo + rem)·2^172 + c_tail
  -- Since rem < d and c_tail < 2^172:
  --   (d·r_lo + rem)·2^172 + c_tail < (d·r_lo + d)·2^172 = d·(r_lo+1)·2^172
  -- So x_norm < m³·2^258 + d·(r_lo+1)·2^172 = R³ + 3R²·(r_lo+1)
  have hx_decomp := x_norm_decomp x_hi_1 x_lo_1 (m * m * m) hcube_le_w
  have hn_full := Nat.div_add_mod (res * 2 ^ 86 + limb_hi) d
  have hx_ub_tight : x_hi_1 * 2 ^ 256 + x_lo_1 <
      m * m * m * 2 ^ 258 + d * (r_lo + 1) * 2 ^ 172 := by
    rw [hx_decomp]
    have : (res * 2 ^ 86 + limb_hi) = d * r_lo + rem_kq := hn_full.symm
    rw [show ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) = d * r_lo + rem_kq from this]
    have : (d * r_lo + rem_kq) * 2 ^ 172 = d * r_lo * 2 ^ 172 + rem_kq * 2 ^ 172 :=
      Nat.add_mul _ _ _
    have : d * (r_lo + 1) * 2 ^ 172 = d * r_lo * 2 ^ 172 + d * 2 ^ 172 := by
      rw [show d * (r_lo + 1) = d * r_lo + d * 1 from Nat.mul_add d r_lo 1, Nat.mul_one,
          Nat.add_mul]
    -- rem < d and c_tail < 2^172, so rem·2^172 + c_tail < d·2^172
    have : rem_kq * 2 ^ 172 + c_tail < d * 2 ^ 172 := by
      have := Nat.mul_lt_mul_of_pos_right hrem_lt (Nat.two_pow_pos 172)
      omega
    omega
  -- Rewrite d·(r_lo+1)·2^172 = 3R²·(r_lo+1)
  have hd_eq_3R2 := d_pow172_eq_3R_sq m
  have hR3 := R_cube_factor m
  have hx_ub_R : x_hi_1 * 2 ^ 256 + x_lo_1 <
      R * R * R + 3 * (R * R) * (r_lo + 1) := by
    have hd_rlo1 : d * (r_lo + 1) * 2 ^ 172 = 3 * (R * R) * (r_lo + 1) := by
      show 3 * (m * m) * (r_lo + 1) * 2 ^ 172 = 3 * (m * 2 ^ 86 * (m * 2 ^ 86)) * (r_lo + 1)
      rw [← hd_eq_3R2]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    calc x_hi_1 * 2 ^ 256 + x_lo_1
        < m * m * m * 2 ^ 258 + d * (r_lo + 1) * 2 ^ 172 := hx_ub_tight
      _ = R * R * R + 3 * (R * R) * (r_lo + 1) := by rw [hR3, hd_rlo1]
  -- ======== Step 4: (r_qc + 1)³ ≥ R³ + 3R²·(r_lo+1) when c ≤ 1 ========
  -- r_qc + 1 = R + r_lo - c + 1 = R + s where s = r_lo - c + 1
  have hrqc1_eq : m * 2 ^ 86 + r_lo - r_lo * r_lo / (m * 2 ^ 86) + 1 = R + (r_lo - c + 1) := by
    show R + r_lo - c + 1 = R + (r_lo - c + 1)
    omega
  rw [hrqc1_eq, cube_sum_expand R (r_lo - c + 1)]
  -- Goal: x_norm < R³ + 3R²·s + 3R·s² + s³ where s = r_lo - c + 1
  -- From hx_ub_R: x_norm < R³ + 3R²·(r_lo + 1)
  -- Suffices: R³ + 3R²·(r_lo+1) ≤ R³ + 3R²·s + 3R·s² + s³
  -- i.e., 3R²·(r_lo+1) ≤ 3R²·s + 3R·s² + s³
  -- s = r_lo - c + 1, so r_lo + 1 = s + c. Thus 3R²(r_lo+1) = 3R²(s+c) = 3R²s + 3R²c.
  -- Need: 3R²c ≤ 3R·s² + s³
  suffices h_suff : R * R * R + 3 * (R * R) * (r_lo + 1) ≤
      R * R * R + 3 * (R * R) * (r_lo - c + 1) +
      3 * R * ((r_lo - c + 1) * (r_lo - c + 1)) +
      (r_lo - c + 1) * (r_lo - c + 1) * (r_lo - c + 1) from
    Nat.lt_of_lt_of_le hx_ub_R h_suff
  -- Split: 3R²(r_lo+1) = 3R²·s + 3R²·c
  have hsc : r_lo - c + 1 + c = r_lo + 1 := by omega
  have h_split : 3 * (R * R) * (r_lo + 1) =
      3 * (R * R) * (r_lo - c + 1) + 3 * (R * R) * c := by
    rw [← Nat.mul_add]; congr 1; exact hsc.symm
  rw [h_split]
  -- Need: 3R²c ≤ 3Rs² + s³
  -- Case split on c
  by_cases hc0 : c = 0
  · -- c = 0: LHS has 3R²·0 = 0 extra, RHS has 3Rs² + s³ ≥ 0 extra. Trivially holds.
    rw [hc0, Nat.mul_zero]; omega
  · -- c = 1 (since c ≤ 1 and c ≠ 0)
    have hc1 : c = 1 := Nat.le_antisymm hc_le1 (Nat.one_le_iff_ne_zero.mpr hc0)
    -- s = r_lo - c + 1 = r_lo (since c = 1)
    have hs_eq : r_lo - c + 1 = r_lo := by omega
    -- Need: 3R²c ≤ 3Rs² + s³, i.e., 3R² ≤ 3R·r_lo² + r_lo³
    -- From c = 1: r_lo² / R ≥ 1, so r_lo² ≥ R.
    have hrlo_sq_ge_R : R ≤ r_lo * r_lo := by
      show m * 2 ^ 86 ≤ r_lo * r_lo
      have hc_ge1 : 1 ≤ r_lo * r_lo / (m * 2 ^ 86) := by
        show 1 ≤ c; omega
      -- 1 ≤ r_lo²/R means R * 1 ≤ r_lo² (from div_mul_le + 1 ≤ quotient)
      calc m * 2 ^ 86
          = (m * 2 ^ 86) * 1 := (Nat.mul_one _).symm
        _ ≤ (m * 2 ^ 86) * (r_lo * r_lo / (m * 2 ^ 86)) := Nat.mul_le_mul_left _ hc_ge1
        _ = r_lo * r_lo / (m * 2 ^ 86) * (m * 2 ^ 86) := Nat.mul_comm _ _
        _ ≤ r_lo * r_lo := Nat.div_mul_le_self _ _
    -- 3R·r_lo² ≥ 3R·R = 3R², so 3R·s² + s³ ≥ 3R² = 3R²·c
    -- Rewrite s = r_lo first (before c = 1 substitution)
    rw [hs_eq]
    rw [hc1, Nat.mul_one]
    -- Goal: R³ + (3R²·r_lo + 3R²) ≤ R³ + 3R²·r_lo + 3R·(r_lo²) + r_lo³
    -- Suffices: 3R² ≤ 3R·(r_lo²) + r_lo³
    -- From 3R·(r_lo²) ≥ 3R·R = 3R²
    have h3RR : 3 * (R * R) = 3 * R * R := by
      simp only [Nat.mul_assoc]
    rw [h3RR]
    have : 3 * R * R ≤ 3 * R * (r_lo * r_lo) := Nat.mul_le_mul_left _ hrlo_sq_ge_R
    omega

-- ============================================================================
-- Sub-lemma A: Lower bound — (r_qc + 1)³ > x_norm
-- ============================================================================

set_option exponentiation.threshold 1024 in
/-- The cube of (r_qc + 2) exceeds x_norm.
    Combined with icbrt_cube_le, this gives icbrt(x_norm) ≤ r_qc + 1.
    Note: the stronger bound icbrt ≤ r_qc does NOT hold for the base r_qc
    when c ≥ 2 (the quadratic correction can over-subtract). The undershoot
    correction in the QC recovers the tighter bound for the actual output.

    Proof: x_norm = R³ + 3R²·r_lo + rem·2^172 + c_tail < R³ + 3R²(r_lo+1) + 2^172.
    (r_qc+2)³ = (R+s')³ where s' = r_lo - c + 2.
    We show 3R²(1-c) + 3R·s'² + s'³ > 2^172, using:
    - For c ≤ 1: 3R²(1-c) ≥ 0 and 12R > 2^172.
    - For c ≥ 2: s'² > R(c-1) since 2(c-2)r_lo < R, giving 3R(s'²-R(c-1)) >> 2^172. -/
private theorem r_qc_succ2_cube_gt (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD) :
    let w := x_hi_1 / 4
    let m := icbrt w
    let res := w - m * m * m
    let d := 3 * (m * m)
    let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
    let r_lo := (res * 2 ^ 86 + limb_hi) / d
    let R := m * 2 ^ 86
    let correction := r_lo * r_lo / R
    let r_qc := R + r_lo - correction
    let x_norm := x_hi_1 * 2 ^ 256 + x_lo_1
    x_norm < (r_qc + 2) * (r_qc + 2) * (r_qc + 2) := by
  simp only
  -- ======== Step 1: Extract base case properties ========
  have hbc := model_cbrtBaseCase_evm_correct x_hi_1 hxhi_lo hxhi_hi
  have hm_lo : 2 ^ 83 ≤ icbrt (x_hi_1 / 4) := hbc.2.2.2.1
  have hm_hi : icbrt (x_hi_1 / 4) < 2 ^ 85 := hbc.2.2.2.2.1
  have hcube_le_w : icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)
      ≤ x_hi_1 / 4 := hbc.2.2.2.2.2.1
  have hres_bound : x_hi_1 / 4 - icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)
      ≤ 3 * (icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)) + 3 * icbrt (x_hi_1 / 4) :=
    hbc.2.2.2.2.2.2.1
  have hd_pos : 3 * (icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)) > 0 :=
    hbc.2.2.2.2.2.2.2.2.2.2
  -- Abbreviate
  let m := icbrt (x_hi_1 / 4)
  let w := x_hi_1 / 4
  let res := w - m * m * m
  let d := 3 * (m * m)
  let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
  let r_lo := (res * 2 ^ 86 + limb_hi) / d
  let R := m * 2 ^ 86
  let c := r_lo * r_lo / R
  let rem_kq := (res * 2 ^ 86 + limb_hi) % d
  let c_tail := x_lo_1 % 2 ^ 172
  -- ======== Step 2: Key bounds ========
  -- R bounds
  have hR_lo : 2 ^ 169 ≤ R :=
    calc 2 ^ 169 = 2 ^ 83 * 2 ^ 86 := by rw [← Nat.pow_add]
      _ ≤ m * 2 ^ 86 := Nat.mul_le_mul_right _ hm_lo
  have hR_lt : R < 2 ^ 171 :=
    calc m * 2 ^ 86
        < 2 ^ 85 * 2 ^ 86 := Nat.mul_lt_mul_of_pos_right hm_hi (Nat.two_pow_pos 86)
      _ = 2 ^ 171 := by rw [← Nat.pow_add]
  have hR_pos : 0 < R := by omega
  -- r_lo < 2^87 (reuse from r_qc_lt_pow172's proof pattern)
  have hlimb_bound : limb_hi < 2 ^ 86 := by
    show (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86
    have hmod4 : x_hi_1 % 4 < 4 := Nat.mod_lt _ (by omega)
    have hdiv : x_lo_1 / 2 ^ 172 < 2 ^ 84 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 172)]
      calc x_lo_1 < WORD_MOD := hxlo
        _ = 2 ^ 84 * 2 ^ 172 := by unfold WORD_MOD; rw [← Nat.pow_add]
    have : (x_hi_1 % 4) * 2 ^ 84 < 2 ^ 86 :=
      calc (x_hi_1 % 4) * 2 ^ 84 < 4 * 2 ^ 84 :=
              Nat.mul_lt_mul_of_pos_right hmod4 (Nat.two_pow_pos 84)
        _ = 2 ^ 86 := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
    omega
  have hr_lo_bound : r_lo < 2 ^ 87 := by
    show (res * 2 ^ 86 + limb_hi) / d < 2 ^ 87
    rw [Nat.div_lt_iff_lt_mul hd_pos]
    have h2m : 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
    calc res * 2 ^ 86 + limb_hi
        < (res + 1) * 2 ^ 86 := by omega
      _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by
          apply Nat.mul_le_mul_right; exact Nat.succ_le_succ hres_bound
      _ ≤ (2 * (3 * (m * m))) * 2 ^ 86 := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ 87 * (3 * (m * m)) := by
          rw [show (2 : Nat) ^ 87 = 2 * 2 ^ 86 from by
            rw [show (87 : Nat) = 1 + 86 from rfl, Nat.pow_add]]; omega
  -- c ≤ r_lo (since r_lo < R)
  have hc_le : c ≤ r_lo := by
    show r_lo * r_lo / R ≤ r_lo
    cases Nat.eq_or_lt_of_le (Nat.zero_le r_lo) with
    | inl h => rw [← h]; simp
    | inr h =>
      exact Nat.le_of_lt ((Nat.div_lt_iff_lt_mul hR_pos).mpr
        (Nat.mul_lt_mul_of_pos_left (by omega : r_lo < R) h))
  -- rem_kq < d
  have hrem_lt : rem_kq < d := Nat.mod_lt _ hd_pos
  -- c_tail < 2^172
  have hctail_lt : c_tail < 2 ^ 172 := Nat.mod_lt _ (Nat.two_pow_pos 172)
  -- ======== Step 3: x_norm upper bound ========
  -- x_norm = m³·2^258 + n_full·2^172 + c_tail (from x_norm_decomp)
  -- where n_full = d·r_lo + rem_kq. Since rem_kq < d and c_tail < 2^172:
  -- x_norm = R³ + (d·r_lo + rem_kq)·2^172 + c_tail < R³ + d·(r_lo+1)·2^172 + 2^172
  have hx_decomp := x_norm_decomp x_hi_1 x_lo_1 (m * m * m) hcube_le_w
  have hn_full := Nat.div_add_mod (res * 2 ^ 86 + limb_hi) d
  -- hn_full : d * r_lo + rem_kq = n_full
  have hrem_ub : rem_kq * 2 ^ 172 + c_tail < d * 2 ^ 172 + 2 ^ 172 := by
    have := Nat.mul_lt_mul_of_pos_right hrem_lt (Nat.two_pow_pos 172)
    omega
  -- x_norm < m³·2^258 + d*(r_lo+1)*2^172 + 2^172
  have hx_ub : x_hi_1 * 2 ^ 256 + x_lo_1 <
      m * m * m * 2 ^ 258 + d * (r_lo + 1) * 2 ^ 172 + 2 ^ 172 := by
    rw [hx_decomp]
    -- LHS = m³·2^258 + n_full·2^172 + c_tail
    -- n_full = d·r_lo + rem_kq, so n_full·2^172 = d·r_lo·2^172 + rem_kq·2^172
    -- Need: d·r_lo·2^172 + rem_kq·2^172 + c_tail < d·(r_lo+1)·2^172 + 2^172
    -- = d·r_lo·2^172 + d·2^172 + 2^172
    -- i.e., rem_kq·2^172 + c_tail < d·2^172 + 2^172 ✓ (from hrem_ub)
    have : (res * 2 ^ 86 + limb_hi) = d * r_lo + rem_kq := hn_full.symm
    -- n_full * 2^172 = (d * r_lo + rem_kq) * 2^172
    rw [show ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) = d * r_lo + rem_kq from this]
    -- Goal: m³·2^258 + (d·r_lo + rem_kq)·2^172 + c_tail < m³·2^258 + d·(r_lo+1)·2^172 + 2^172
    have : (d * r_lo + rem_kq) * 2 ^ 172 = d * r_lo * 2 ^ 172 + rem_kq * 2 ^ 172 :=
      Nat.add_mul _ _ _
    have : d * (r_lo + 1) * 2 ^ 172 = d * r_lo * 2 ^ 172 + d * 2 ^ 172 := by
      rw [show d * (r_lo + 1) = d * r_lo + d * 1 from Nat.mul_add d r_lo 1, Nat.mul_one,
          Nat.add_mul]
    omega
  -- ======== Step 4: (R + s')³ > R³ + d·(r_lo+1)·2^172 + 2^172 ========
  -- Using R³ = m³·2^258, d·2^172 = 3R², this is:
  -- (R + s')³ > R³ + 3R²·(r_lo+1) + 2^172
  -- Expand: 3R²·s' + 3R·s'² + s'³ > 3R²·(r_lo+1) + 2^172
  -- i.e., 3R²·(s' - r_lo - 1) + 3R·s'² + s'³ > 2^172
  -- i.e., 3R²·(1 - c) + 3R·s'² + s'³ > 2^172  (in Int)
  -- But we need to connect d·(r_lo+1)·2^172 to 3R²·(r_lo+1):
  have hd_eq_3R2 := d_pow172_eq_3R_sq m
  -- d·2^172 = 3R² (definitionally via hd_eq_3R2)
  -- So d·(r_lo+1)·2^172 = 3R²·(r_lo+1)
  -- Goal: (R + s')³ > m³·2^258 + d·(r_lo+1)·2^172 + 2^172
  -- = R³ + 3R²·(r_lo+1) + 2^172  (using R³ = m³·2^258 and d·2^172 = 3R²)
  -- Key: r_qc + 2 = R + r_lo - c + 2 = R + s'  (Nat subtraction is fine since c ≤ r_lo)
  have hrqc2_eq : m * 2 ^ 86 + r_lo - r_lo * r_lo / (m * 2 ^ 86) + 2 = R + (r_lo - c + 2) := by
    show R + r_lo - c + 2 = R + (r_lo - c + 2)
    omega
  rw [hrqc2_eq]
  -- Expand cube
  rw [cube_sum_expand R (r_lo - c + 2)]
  -- RHS = R³ + 3R²·s' + 3R·s'² + s'³
  -- Need: R³ + 3R²·(r_lo+1) + 2^172 + ... < R³ + 3R²·s' + 3R·s'² + s'³
  -- But we're comparing x_norm (via hx_ub) to the expanded cube.
  -- Combine hx_ub with the goal.
  -- Goal is now: x_hi_1 * 2^256 + x_lo_1 < R³ + 3R²·s' + 3R·s'² + s'³
  -- From hx_ub: x_hi_1 * 2^256 + x_lo_1 < m³·2^258 + d·(r_lo+1)·2^172 + 2^172
  -- Suffices: m³·2^258 + d·(r_lo+1)·2^172 + 2^172 ≤ R³ + 3R²·s' + 3R·s'² + s'³
  -- i.e., R³ + 3R²·(r_lo+1) + 2^172 ≤ R³ + 3R²·s' + 3R·s'² + s'³
  -- i.e., 3R²·(r_lo+1) + 2^172 ≤ 3R²·s' + 3R·s'² + s'³
  -- Since s' = r_lo - c + 2 ≥ r_lo + 1 when c ≤ 1, and for c ≥ 2 the s'² term dominates
  -- Rewrite RHS using hR3 and hd_eq_3R2
  have hR3 := R_cube_factor m
  -- R³ = m³ · 2^258
  -- d·(r_lo+1)·2^172 = d·2^172·(r_lo+1) = 3R²·(r_lo+1)
  -- 3R² = 3·(R·R) = 3·(m·2^86)·(m·2^86)
  -- Need to show: m³·2^258 + d·(r_lo+1)·2^172 + 2^172 ≤ R·R·R + 3·(R·R)·s' + 3·R·(s'·s') + s'·s'·s'
  -- Rewrite R·R·R = m³·2^258
  -- And 3·(R·R)·(r_lo+1) = d·(r_lo+1)·2^172 (from hd_eq_3R2)
  -- Hmm, this requires careful Nat equalities. Let me use calc.
  suffices h_suff : m * m * m * 2 ^ 258 + d * (r_lo + 1) * 2 ^ 172 + 2 ^ 172 ≤
      R * R * R + 3 * (R * R) * (r_lo - c + 2) + 3 * R * ((r_lo - c + 2) * (r_lo - c + 2)) +
      (r_lo - c + 2) * (r_lo - c + 2) * (r_lo - c + 2) from
    Nat.lt_of_lt_of_le hx_ub h_suff
  -- s' ≥ 2 (needed inside the suffices proof)
  have hs'_ge_2 : 2 ≤ r_lo - c + 2 := by omega
  -- Rewrite m³·2^258 = R³
  rw [← hR3]
  -- Rewrite d·(r_lo+1)·2^172: d·2^172 = 3·(R·R), so d·(r_lo+1)·2^172 = 3·(R·R)·(r_lo+1)
  -- d·(r_lo+1)·2^172 = d·2^172·(r_lo+1) (associativity)
  have hd_rlo1 : d * (r_lo + 1) * 2 ^ 172 = 3 * (R * R) * (r_lo + 1) := by
    show 3 * (m * m) * (r_lo + 1) * 2 ^ 172 = 3 * (m * 2 ^ 86 * (m * 2 ^ 86)) * (r_lo + 1)
    rw [← hd_eq_3R2]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hd_rlo1]
  -- Goal: R³ + 3R²·(r_lo+1) + 2^172 ≤ R³ + 3R²·s' + 3R·s'² + s'³
  -- Cancel R³
  -- Need: 3R²·(r_lo+1) + 2^172 ≤ 3R²·s' + 3R·s'² + s'³
  -- Case split on c
  by_cases hc_le1 : c ≤ 1
  · -- Case c ≤ 1: s' = r_lo - c + 2 ≥ r_lo + 1
    have hs'_ge_rlo1 : r_lo + 1 ≤ r_lo - c + 2 := by omega
    -- 3R²·(r_lo+1) ≤ 3R²·s'
    have h1 : 3 * (R * R) * (r_lo + 1) ≤ 3 * (R * R) * (r_lo - c + 2) :=
      Nat.mul_le_mul_left _ hs'_ge_rlo1
    -- 3R·s'² ≥ 3R·4 = 12R > 2^172
    have h_s'sq : 4 ≤ (r_lo - c + 2) * (r_lo - c + 2) := Nat.mul_le_mul hs'_ge_2 hs'_ge_2
    have h_12R : 2 ^ 172 ≤ 12 * R := by
      calc 2 ^ 172 = 2 * 2 ^ 171 := by rw [show (172 : Nat) = 1 + 171 from rfl, Nat.pow_add]
        _ ≤ 2 * (6 * R) := Nat.mul_le_mul_left _ (by omega)
        _ = 12 * R := by omega
    have h_3Rs'2 : 2 ^ 172 ≤ 3 * R * ((r_lo - c + 2) * (r_lo - c + 2)) :=
      calc 2 ^ 172 ≤ 12 * R := h_12R
        _ = 3 * R * 4 := by omega
        _ ≤ 3 * R * ((r_lo - c + 2) * (r_lo - c + 2)) := Nat.mul_le_mul_left _ h_s'sq
    -- Chain: R³ + 3R²(r_lo+1) + 2^172 ≤ R³ + 3R²s' + 3Rs'² ≤ R³ + 3R²s' + 3Rs'² + s'³
    have step1 : R * R * R + 3 * (R * R) * (r_lo + 1) + 2 ^ 172 ≤
        R * R * R + 3 * (R * R) * (r_lo - c + 2) + 3 * R * ((r_lo - c + 2) * (r_lo - c + 2)) :=
      Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) h1) h_3Rs'2
    exact Nat.le_trans step1 (Nat.le_add_right _ _)
  · -- Case c ≥ 2: s'² > R(c-1) since 2cr_lo < R
    have hc_ge2 : 2 ≤ c := by omega
    have hcR_le : c * R ≤ r_lo * r_lo := Nat.div_mul_le_self _ _
    -- Bound c*r_lo: from c*R ≤ r_lo², c*r_lo*R ≤ r_lo³ < 2^261, so c*r_lo < 2^92
    -- c*r_lo ≤ r_lo²/R * r_lo ≤ r_lo³/R < 2^261/2^169 = 2^92
    -- Direct approach: c ≤ r_lo (from hc_le), so c*r_lo ≤ r_lo².
    -- Also c*R ≤ r_lo², so c ≤ r_lo²/R < (2^87)²/2^169 = 2^174/2^169 = 2^5 = 32.
    have hc_lt_32 : c < 32 := by
      -- c*R ≤ r_lo² < (2^87)² = 2^174, and R ≥ 2^169
      have : c * R < 2 ^ 174 := Nat.lt_of_le_of_lt hcR_le
        (calc r_lo * r_lo
            ≤ r_lo * 2 ^ 87 := Nat.mul_le_mul_left _ (Nat.le_of_lt hr_lo_bound)
          _ < 2 ^ 87 * 2 ^ 87 := Nat.mul_lt_mul_of_pos_right hr_lo_bound (Nat.two_pow_pos 87)
          _ = 2 ^ 174 := by rw [← Nat.pow_add])
      -- c < 2^174 / R ≤ 2^174 / 2^169 = 2^5 = 32
      have h174 : (2 : Nat) ^ 174 = 32 * 2 ^ 169 := by
        rw [show (174 : Nat) = 5 + 169 from rfl, Nat.pow_add]
      by_cases hc0 : c = 0; · omega
      · exact Nat.lt_of_mul_lt_mul_right
          (calc c * R < 2 ^ 174 := ‹_›
            _ = 32 * 2 ^ 169 := h174
            _ ≤ 32 * R := Nat.mul_le_mul_left _ hR_lo)
    -- c*r_lo < 32 * 2^87 = 2^92
    have hcr_lt : c * r_lo < 2 ^ 92 :=
      calc c * r_lo < 32 * r_lo := Nat.mul_lt_mul_of_pos_right hc_lt_32 (by omega)
        _ ≤ 32 * 2 ^ 87 := Nat.mul_le_mul_left _ (Nat.le_of_lt hr_lo_bound)
        _ = 2 ^ 92 := by rw [show (32 : Nat) = 2 ^ 5 from rfl, ← Nat.pow_add]
    -- 2*c*r_lo < R (since 2 * 2^92 = 2^93 ≤ 2^169 ≤ R)
    have h2cr : 2 * c * r_lo < R := by
      calc 2 * c * r_lo = 2 * (c * r_lo) := Nat.mul_assoc 2 c r_lo
        _ < 2 * 2 ^ 92 := Nat.mul_lt_mul_of_pos_left hcr_lt (by omega)
        _ = 2 ^ 93 := by rw [show (93 : Nat) = 1 + 92 from rfl, Nat.pow_add]
        _ ≤ R := Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega : 93 ≤ 169)) hR_lo
    -- Key algebraic identity: (r_lo-c)² + 2cr_lo = r_lo² + c²
    have hsq_id : (r_lo - c) * (r_lo - c) + 2 * c * r_lo = r_lo * r_lo + c * c := by
      suffices h : (↑((r_lo - c) * (r_lo - c) + 2 * c * r_lo) : Int) =
          ↑(r_lo * r_lo + c * c) by exact_mod_cast h
      push_cast
      have hsub : (↑(r_lo - c) : Int) = ↑r_lo - ↑c := by omega
      rw [hsub]
      simp only [show (2 : Int) = 1 + 1 from rfl,
                 Int.add_mul, Int.one_mul,
                 Int.sub_mul, Int.mul_sub]
      simp only [Int.mul_comm]; omega
    -- R(c-1) + R = Rc ≤ r_lo²
    have hRc1_R : R * (c - 1) + R ≤ r_lo * r_lo := by
      -- c ≥ 2, so c - 1 + 1 = c. Then R*(c-1) + R = R*((c-1)+1) = R*c ≤ r_lo²
      calc R * (c - 1) + R
          = R * (c - 1) + R * 1 := by rw [Nat.mul_one]
        _ = R * (c - 1 + 1) := (Nat.mul_add R (c - 1) 1).symm
        _ = R * c := by congr 1; omega
        _ = c * R := Nat.mul_comm R c
        _ ≤ r_lo * r_lo := hcR_le
    -- (r_lo-c)² ≥ R(c-1) + 1 (since (r_lo-c)² ≥ r_lo² - 2cr_lo ≥ R(c-1) + R - 2cr_lo > R(c-1))
    have hrlc_sq : R * (c - 1) + 1 ≤ (r_lo - c) * (r_lo - c) := by
      -- From hsq_id: (r_lo-c)² = r_lo² + c² - 2cr_lo ≥ r_lo² - 2cr_lo
      -- From hRc1_R: R(c-1) + R ≤ r_lo²
      -- From h2cr: 2cr_lo < R
      -- So (r_lo-c)² ≥ r_lo² - 2cr_lo ≥ (R(c-1) + R) - 2cr_lo > R(c-1)
      have : r_lo * r_lo ≤ (r_lo - c) * (r_lo - c) + 2 * c * r_lo := by
        rw [hsq_id]; omega
      omega
    -- (r_lo-c+2)² ≥ (r_lo-c)² + 4
    have hs'sq_ge : (r_lo - c) * (r_lo - c) + 4 ≤ (r_lo - c + 2) * (r_lo - c + 2) := by
      -- (a+2)² = a² + 4a + 4 ≥ a² + 4
      -- In Nat: (r_lo - c + 2)² ≥ (r_lo - c)² + 4 since r_lo - c ≥ 0
      have h : (r_lo - c + 2) * (r_lo - c + 2) =
          (r_lo - c) * (r_lo - c) + 4 * (r_lo - c) + 4 := by
        suffices hi : (↑((r_lo - c + 2) * (r_lo - c + 2)) : Int) =
            ↑((r_lo - c) * (r_lo - c) + 4 * (r_lo - c) + 4) by exact_mod_cast hi
        push_cast
        have hsub : (↑(r_lo - c) : Int) = ↑r_lo - ↑c := by omega
        rw [hsub]
        simp only [show (4 : Int) = 2 * 2 from rfl, show (2 : Int) = 1 + 1 from rfl,
                   Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one,
                   Int.sub_mul, Int.mul_sub]
        simp only [Int.mul_comm]; omega
      omega
    -- s'² ≥ R(c-1) + 5
    have hs'sq_bound : R * (c - 1) + 5 ≤ (r_lo - c + 2) * (r_lo - c + 2) := by omega
    -- 3R·s'² ≥ 3R·(R(c-1) + 5) = 3R²(c-1) + 15R
    have h_3R_mul : 3 * R * (R * (c - 1) + 5) ≤
        3 * R * ((r_lo - c + 2) * (r_lo - c + 2)) := Nat.mul_le_mul_left _ hs'sq_bound
    -- 15R ≥ 2^172
    have h15R : 2 ^ 172 ≤ 15 * R := by
      calc 2 ^ 172 = 8 * 2 ^ 169 := by
            rw [show (172 : Nat) = 3 + 169 from rfl, Nat.pow_add]
        _ ≤ 8 * R := Nat.mul_le_mul_left _ hR_lo
        _ ≤ 15 * R := Nat.mul_le_mul_right _ (by omega)
    -- Split 3R²(r_lo+1) = 3R²·s' + 3R²(c-1)
    have hrlo1_split : 3 * (R * R) * (r_lo + 1) =
        3 * (R * R) * (r_lo - c + 2) + 3 * (R * R) * (c - 1) := by
      rw [← Nat.mul_add]; congr 1; omega
    rw [hrlo1_split]
    -- Rewrite 3R²(c-1) = 3R·(R·(c-1))
    have hRR_assoc : 3 * (R * R) * (c - 1) = 3 * R * (R * (c - 1)) := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm]
    rw [hRR_assoc]
    -- Goal: 3R²s' + 3R(R(c-1)) + 2^172 ≤ 3R²s' + 3Rs'² + s'³
    -- Need: 3R(R(c-1)) + 2^172 ≤ 3Rs'² + s'³
    -- From h_3R_mul: 3R(R(c-1)) + 15R ≤ 3Rs'²
    -- From h15R: 2^172 ≤ 15R
    -- So 3R(R(c-1)) + 2^172 ≤ 3R(R(c-1)) + 15R ≤ 3Rs'² ≤ 3Rs'² + s'³
    have step1 : 3 * R * (R * (c - 1)) + 2 ^ 172 ≤
        3 * R * (R * (c - 1)) + 15 * R := by omega
    have step2 : 3 * R * (R * (c - 1)) + 15 * R ≤
        3 * R * ((r_lo - c + 2) * (r_lo - c + 2)) := by
      -- 3R(R(c-1) + 5) ≤ 3Rs'² from h_3R_mul, and R(c-1) + 5 ≤ R(c-1) + 15R/3R...
      -- Actually: 3R·(R(c-1) + 5) = 3R·R(c-1) + 15R
      -- And h_3R_mul says 3R·(R(c-1) + 5) ≤ 3R·s'²
      calc 3 * R * (R * (c - 1)) + 15 * R
          = 3 * R * (R * (c - 1)) + 3 * R * 5 := by omega
        _ = 3 * R * (R * (c - 1) + 5) := (Nat.mul_add (3 * R) _ 5).symm
        _ ≤ 3 * R * ((r_lo - c + 2) * (r_lo - c + 2)) := h_3R_mul
    calc R * R * R + (3 * (R * R) * (r_lo - c + 2) + 3 * R * (R * (c - 1))) + 2 ^ 172
        ≤ R * R * R + (3 * (R * R) * (r_lo - c + 2) +
            3 * R * ((r_lo - c + 2) * (r_lo - c + 2))) := by
          have := Nat.le_trans step1 step2; omega
      _ ≤ R * R * R + 3 * (R * R) * (r_lo - c + 2) +
            3 * R * ((r_lo - c + 2) * (r_lo - c + 2)) +
            (r_lo - c + 2) * (r_lo - c + 2) * (r_lo - c + 2) := by omega

-- ============================================================================
-- Sub-lemma B: Upper bound — (r_qc - 1)³ ≤ x_norm
-- ============================================================================

/-- The cube of (r_qc - 1) does not exceed x_norm.
    Combined with icbrt_lt_succ_cube, this gives r_qc ≤ icbrt(x_norm) + 1.
    Note: r_qc ≥ 1 since r_qc ≥ R = m·2^86 ≥ 2^169.
    Proof sketch: x_norm - (r_qc-1)³ = 3R²(c+1) + S - 3R(q-1)² - (q-1)³
    where S = rem·2^172 + c_tail ≥ 0. Since 3R²(c+1) > 3R·r_lo² ≥ 3R(q-1)²
    and the surplus 3R[R(c+1) - (q-1)²] grows quadratically in r_lo while
    (q-1)³ grows cubically but with r_lo/R ≪ 1, the surplus dominates. -/
private theorem r_qc_pred_cube_le (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD) :
    let w := x_hi_1 / 4
    let m := icbrt w
    let res := w - m * m * m
    let d := 3 * (m * m)
    let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
    let r_lo := (res * 2 ^ 86 + limb_hi) / d
    let R := m * 2 ^ 86
    let correction := r_lo * r_lo / R
    let r_qc := R + r_lo - correction
    let x_norm := x_hi_1 * 2 ^ 256 + x_lo_1
    (r_qc - 1) * (r_qc - 1) * (r_qc - 1) ≤ x_norm := by
  simp only
  -- ======== Step 1: Extract base case properties ========
  have hbc := model_cbrtBaseCase_evm_correct x_hi_1 hxhi_lo hxhi_hi
  have hm_lo : 2 ^ 83 ≤ icbrt (x_hi_1 / 4) := hbc.2.2.2.1
  have hm_hi : icbrt (x_hi_1 / 4) < 2 ^ 85 := hbc.2.2.2.2.1
  have hcube_le_w : icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)
      ≤ x_hi_1 / 4 := hbc.2.2.2.2.2.1
  have hres_bound : x_hi_1 / 4 - icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)
      ≤ 3 * (icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)) + 3 * icbrt (x_hi_1 / 4) :=
    hbc.2.2.2.2.2.2.1
  have hd_pos : 3 * (icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)) > 0 :=
    hbc.2.2.2.2.2.2.2.2.2.2
  -- Abbreviate
  let m := icbrt (x_hi_1 / 4)
  let w := x_hi_1 / 4
  let res := w - m * m * m
  let d := 3 * (m * m)
  let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
  let r_lo := (res * 2 ^ 86 + limb_hi) / d
  let R := m * 2 ^ 86
  let c := r_lo * r_lo / R
  let rem_kq := (res * 2 ^ 86 + limb_hi) % d
  let c_tail := x_lo_1 % 2 ^ 172
  -- ======== Step 2: Key bounds ========
  have hR_pos : 0 < R := by omega
  have hlimb_bound : limb_hi < 2 ^ 86 := by
    show (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86
    have hmod4 : x_hi_1 % 4 < 4 := Nat.mod_lt _ (by omega)
    have hdiv : x_lo_1 / 2 ^ 172 < 2 ^ 84 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 172)]
      calc x_lo_1 < WORD_MOD := hxlo
        _ = 2 ^ 84 * 2 ^ 172 := by unfold WORD_MOD; rw [← Nat.pow_add]
    have : (x_hi_1 % 4) * 2 ^ 84 < 2 ^ 86 :=
      calc (x_hi_1 % 4) * 2 ^ 84 < 4 * 2 ^ 84 :=
              Nat.mul_lt_mul_of_pos_right hmod4 (Nat.two_pow_pos 84)
        _ = 2 ^ 86 := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
    omega
  have hr_lo_bound : r_lo < 2 ^ 87 := by
    show (res * 2 ^ 86 + limb_hi) / d < 2 ^ 87
    rw [Nat.div_lt_iff_lt_mul hd_pos]
    have h2m : 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
    calc res * 2 ^ 86 + limb_hi
        < (res + 1) * 2 ^ 86 := by omega
      _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by
          apply Nat.mul_le_mul_right; exact Nat.succ_le_succ hres_bound
      _ ≤ (2 * (3 * (m * m))) * 2 ^ 86 := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ 87 * (3 * (m * m)) := by
          rw [show (2 : Nat) ^ 87 = 2 * 2 ^ 86 from by
            rw [show (87 : Nat) = 1 + 86 from rfl, Nat.pow_add]]; omega
  -- Floor division bound: r_lo² < (c+1)R
  have hcR_lt : r_lo * r_lo < (c + 1) * R := by
    show r_lo * r_lo < (r_lo * r_lo / R + 1) * R
    have hdm := Nat.div_add_mod (r_lo * r_lo) R
    -- hdm : R * (r_lo * r_lo / R) + r_lo * r_lo % R = r_lo * r_lo
    have hmod_lt := Nat.mod_lt (r_lo * r_lo) hR_pos
    -- (c + 1) * R = c * R + R = R * c + R
    calc r_lo * r_lo
        = R * (r_lo * r_lo / R) + r_lo * r_lo % R := hdm.symm
      _ < R * (r_lo * r_lo / R) + R := by omega
      _ = R * (r_lo * r_lo / R + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = (r_lo * r_lo / R + 1) * R := Nat.mul_comm _ _
  -- ======== Step 3: x_norm lower bound ========
  -- x_norm = R³ + n_full·2^172 + c_tail where n_full = d·r_lo + rem_kq
  -- x_norm ≥ R³ + d·r_lo·2^172 = R³ + 3R²·r_lo
  have hx_decomp := x_norm_decomp x_hi_1 x_lo_1 (m * m * m) hcube_le_w
  have hn_full := Nat.div_add_mod (res * 2 ^ 86 + limb_hi) d
  have h_num_eq : (res * 2 ^ 86 + limb_hi) = d * r_lo + rem_kq := hn_full.symm
  have h_num_mul : (d * r_lo + rem_kq) * 2 ^ 172 = d * r_lo * 2 ^ 172 + rem_kq * 2 ^ 172 :=
    Nat.add_mul _ _ _
  have hx_lb : m * m * m * 2 ^ 258 + d * r_lo * 2 ^ 172 ≤
      x_hi_1 * 2 ^ 256 + x_lo_1 := by
    rw [hx_decomp]
    rw [show ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) = d * r_lo + rem_kq from h_num_eq]
    rw [h_num_mul]
    omega
  -- Rewrite using R³ = m³·2^258 and 3R² = d·2^172
  have hR3 := R_cube_factor m
  have hd_eq_3R2 := d_pow172_eq_3R_sq m
  -- x_norm ≥ R³ + 3R²·r_lo
  have hx_lb2 : R * R * R + 3 * (R * R) * r_lo ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := by
    calc R * R * R + 3 * (R * R) * r_lo
        = m * m * m * 2 ^ 258 + 3 * (m * m) * r_lo * 2 ^ 172 := by
          rw [← hR3]
          show R * R * R + 3 * (R * R) * r_lo =
            R * R * R + 3 * (m * m) * r_lo * 2 ^ 172
          rw [← hd_eq_3R2]
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ = m * m * m * 2 ^ 258 + d * r_lo * 2 ^ 172 := by rfl
      _ ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := hx_lb
  -- ======== Step 4: Case split ========
  -- r_qc - 1 = R + r_lo - c - 1
  -- Need to show (R + r_lo - c - 1)³ ≤ x_norm
  by_cases hrloc : r_lo ≤ c
  · -- Trivial case: r_lo ≤ c → r_qc - 1 ≤ R - 1, and (R-1)³ ≤ R³ ≤ x_norm
    have hrqc1_le : R + r_lo - c - 1 ≤ R - 1 := by omega
    have hR1_le : R - 1 ≤ R := Nat.sub_le _ _
    calc (R + r_lo - c - 1) * (R + r_lo - c - 1) * (R + r_lo - c - 1)
        ≤ (R - 1) * (R - 1) * (R - 1) := cube_monotone hrqc1_le
      _ ≤ R * R * R :=
          Nat.mul_le_mul (Nat.mul_le_mul hR1_le hR1_le) hR1_le
      _ ≤ R * R * R + 3 * (R * R) * r_lo := Nat.le_add_right _ _
      _ ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := hx_lb2
  · -- Main case: r_lo ≥ c + 1
    -- Let t = r_lo - c - 1 (≥ 0). Then r_qc - 1 = R + t.
    -- Need: (R + t)³ ≤ x_norm where t = r_lo - c - 1.
    -- Expand: (R + t)³ = R³ + 3R²t + 3Rt² + t³
    -- From x_norm ≥ R³ + 3R²·r_lo, suffices: 3R²t + 3Rt² + t³ ≤ 3R²·r_lo
    -- i.e., 3R²(r_lo - t) ≥ 3Rt² + t³, i.e., 3R²(c+1) ≥ 3Rt² + t³
    have hrqc1_eq : R + r_lo - c - 1 = R + (r_lo - c - 1) := by omega
    rw [hrqc1_eq, cube_sum_expand R (r_lo - c - 1)]
    -- Goal: R³ + 3R²·t + 3R·t² + t³ ≤ x_norm
    -- Suffices: 3R²·t + 3R·t² + t³ ≤ 3R²·r_lo (since R³ + 3R²·r_lo ≤ x_norm)
    suffices h_suff : 3 * (R * R) * (r_lo - c - 1) +
        3 * R * ((r_lo - c - 1) * (r_lo - c - 1)) +
        (r_lo - c - 1) * (r_lo - c - 1) * (r_lo - c - 1) ≤
        3 * (R * R) * r_lo from
      calc R * R * R + 3 * (R * R) * (r_lo - c - 1) +
            3 * R * ((r_lo - c - 1) * (r_lo - c - 1)) +
            (r_lo - c - 1) * (r_lo - c - 1) * (r_lo - c - 1)
          ≤ R * R * R + 3 * (R * R) * r_lo := by omega
        _ ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := hx_lb2
    -- Reduce: 3R²·t + 3Rt² + t³ ≤ 3R²·r_lo
    -- ↔ 3Rt² + t³ ≤ 3R²(r_lo - t) = 3R²(c + 1)
    -- Since r_lo - t = r_lo - (r_lo - c - 1) = c + 1
    -- Rewrite 3R²·r_lo = 3R²·t + 3R²·(c+1)
    have hrlo_split : 3 * (R * R) * r_lo =
        3 * (R * R) * (r_lo - c - 1) + 3 * (R * R) * (c + 1) := by
      rw [← Nat.mul_add]; congr 1; omega
    rw [hrlo_split]
    -- Cancel 3R²·t from both sides. Need: 3Rt² + t³ ≤ 3R²(c+1)
    -- Suffices to prove this
    suffices h_core : 3 * R * ((r_lo - c - 1) * (r_lo - c - 1)) +
        (r_lo - c - 1) * (r_lo - c - 1) * (r_lo - c - 1) ≤
        3 * (R * R) * (c + 1) by omega
    -- t² ≤ r_lo² < (c+1)R; t < 2^87; t³ < 2^87·(c+1)R ≤ 3R·(c+1)R = 3R²(c+1)
    have ht_le_rlo : r_lo - c - 1 ≤ r_lo := Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)
    have ht_sq_lt_cR : (r_lo - c - 1) * (r_lo - c - 1) < (c + 1) * R :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul ht_le_rlo ht_le_rlo) hcR_lt
    -- Use sq_sum_expand: r_lo = t + (c+1), so r_lo² = t² + 2t(c+1) + (c+1)².
    -- From (c+1)R > r_lo²: (c+1)R - t² > 2t(c+1).
    -- Then: 3R((c+1)R - t²) > 6Rt(c+1) ≥ t(c+1)R > t·t² = t³.
    -- So 3Rt² + t³ < 3Rt² + 3R((c+1)R - t²) = 3R(c+1)R = 3R²(c+1).
    have hrlo_eq : r_lo = (r_lo - c - 1) + (c + 1) := by omega
    have hrlo_sq := sq_sum_expand (r_lo - c - 1) (c + 1)
    have h_gap : (r_lo - c - 1) * (r_lo - c - 1) + 2 * (r_lo - c - 1) * (c + 1) <
        (c + 1) * R := by
      have : (r_lo - c - 1 + (c + 1)) * (r_lo - c - 1 + (c + 1)) =
          (r_lo - c - 1) * (r_lo - c - 1) + 2 * (r_lo - c - 1) * (c + 1) +
          (c + 1) * (c + 1) := hrlo_sq
      rw [← hrlo_eq] at this; omega
    cases Nat.eq_or_lt_of_le (Nat.zero_le (r_lo - c - 1)) with
    | inl ht0 =>
      -- t = 0: everything is 0 ≤ 3R²(c+1)
      rw [← ht0]; simp
    | inr ht_pos =>
      -- t ≥ 1, where t = r_lo - c - 1. Strategy: show t³ < 3R·((c+1)R - t²),
      -- then 3Rt² + t³ < 3Rt² + 3R·((c+1)R - t²) = 3R·(c+1)R = 3R²·(c+1).
      -- Rewrite t*t*t = t*(t*t) for associativity
      rw [show (r_lo - c - 1) * (r_lo - c - 1) * (r_lo - c - 1) =
          (r_lo - c - 1) * ((r_lo - c - 1) * (r_lo - c - 1)) from Nat.mul_assoc _ _ _]
      -- t·t² < t·(c+1)R (from ht_sq_lt_cR)
      have ht_cube_bound : (r_lo - c - 1) * ((r_lo - c - 1) * (r_lo - c - 1)) <
          (r_lo - c - 1) * ((c + 1) * R) :=
        Nat.mul_lt_mul_of_pos_left ht_sq_lt_cR ht_pos
      -- Key: t·(c+1)·R ≤ 2t(c+1)·R  (trivially: a ≤ 2a)
      -- Then: 2t(c+1)·R < ((c+1)R - t²)·R  (from h_gap, mul by R)
      -- Then: ((c+1)R-t²)·R ≤ R·((c+1)R-t²) = 1·R·((c+1)R-t²) ≤ 3R·((c+1)R-t²)
      -- So: t·(c+1)R < 3R·((c+1)R - t²), hence t³ < t·(c+1)R < 3R·((c+1)R - t²).
      -- We prove: (r_lo-c-1) * ((c+1)*R) < 3 * R * ((c+1)*R - t²)
      -- by showing: a*b*c < (a*b - d) * c ≤ 3c * (a*b - d) where appropriate.
      -- Actually let's just show t³ < 3R * ((c+1)R - t²) directly.
      -- From h_gap: 2*t*(c+1) < (c+1)*R - t², so (c+1)*R - t² > 2*t*(c+1) ≥ 2*t
      -- Since 3R ≥ 3*2^169 and t < 2^87, we have 3R*((c+1)R - t²) > 3R*2t > 6R*t > t*(c+1)R > t³
      -- But these chains involve nonlinear reasoning that omega can't do.
      -- Simplest working approach: show it all as one calc chain using Nat mul lemmas.
      -- t³ = t*t² < t*(c+1)R  [from ht_cube_bound]
      --    ≤ (c+1)*R*t  [comm]  -- actually same thing
      -- We need (r_lo-c-1)*((c+1)*R) < 3*R*((c+1)*R - (r_lo-c-1)*(r_lo-c-1))
      -- i.e., t*(c+1)*R < 3R*((c+1)*R - t²)
      -- i.e., t*(c+1) < 3*((c+1)*R - t²)  [div by R, but careful with Nat]
      -- From h_gap: (c+1)*R - t² > 2*t*(c+1) ≥ t*(c+1)
      -- So 3*((c+1)*R - t²) > 3*t*(c+1) > t*(c+1). Not quite what we need.
      -- Actually: t*(c+1)*R = t*(c+1) * R. And 3R * ((c+1)R - t²) = 3 * R * ((c+1)*R - t²).
      -- Need: t*(c+1)*R < 3*R*((c+1)*R - t²)
      -- ↔ t*(c+1) < 3*((c+1)*R - t²)  [cancel R; safe since R > 0]
      -- From h_gap: (c+1)*R - t² > t² + 2t(c+1) - t² + something... wait:
      -- h_gap says t² + 2t(c+1) < (c+1)*R, so (c+1)*R - t² > 2t(c+1).
      -- 3*((c+1)*R - t²) > 3*2*t*(c+1) = 6t(c+1) > t(c+1).
      -- So the inequality holds. Let's formalize with Nat.div.
      -- Actually, just prove it directly without dividing:
      -- t*(c+1)*R ≤ 2*t*(c+1)*R  [x ≤ 2x for Nat]
      --          < ((c+1)*R - t²)*R  [h_gap * R]
      --          ≤ 3*R*((c+1)*R - t²)  [a*R ≤ 3R*a, i.e., R ≤ 3R]
      -- Chain using Nat.mul_lt_mul_of_pos_right and omega.
      -- For step 1: t*(c+1)*R = Nat.mul_assoc: (r_lo-c-1) * ((c+1) * R) = ((r_lo-c-1)*(c+1)) * R
      have hassoc1 : (r_lo - c - 1) * ((c + 1) * R) = (r_lo - c - 1) * (c + 1) * R :=
        (Nat.mul_assoc _ _ _).symm
      -- For step 2 lhs: 2*t*(c+1)*R = (2*(r_lo-c-1)*(c+1)) * R
      -- h_gap : (r_lo-c-1)*(r_lo-c-1) + 2*(r_lo-c-1)*(c+1) < (c+1)*R
      -- Multiply by R: (2*(r_lo-c-1)*(c+1)) * R < ((c+1)*R - (r_lo-c-1)*(r_lo-c-1)) * R
      have h_gap2 : 2 * (r_lo - c - 1) * (c + 1) <
          (c + 1) * R - (r_lo - c - 1) * (r_lo - c - 1) := by omega
      have hstep2 : 2 * (r_lo - c - 1) * (c + 1) * R <
          ((c + 1) * R - (r_lo - c - 1) * (r_lo - c - 1)) * R :=
        Nat.mul_lt_mul_of_pos_right h_gap2 (by omega)
      -- Now combine:
      -- t*(c+1)*R = (t*(c+1))*R ≤ (2*t*(c+1))*R < ((c+1)*R - t²)*R ≤ 3R*((c+1)*R - t²)
      have hchain : (r_lo - c - 1) * ((c + 1) * R) <
          3 * R * ((c + 1) * R - (r_lo - c - 1) * (r_lo - c - 1)) := by
        rw [hassoc1]
        calc (r_lo - c - 1) * (c + 1) * R
            ≤ 2 * (r_lo - c - 1) * (c + 1) * R :=
              Nat.mul_le_mul_right R
                (Nat.mul_le_mul_right (c + 1) (Nat.le_mul_of_pos_left _ (by omega)))
          _ < ((c + 1) * R - (r_lo - c - 1) * (r_lo - c - 1)) * R := hstep2
          _ = R * ((c + 1) * R - (r_lo - c - 1) * (r_lo - c - 1)) := Nat.mul_comm _ _
          _ ≤ 3 * R * ((c + 1) * R - (r_lo - c - 1) * (r_lo - c - 1)) :=
              Nat.mul_le_mul_right _
                (Nat.le_mul_of_pos_left R (by omega))
      -- Split 3R(c+1)R = 3Rt² + 3R((c+1)R - t²)
      have h_sum : 3 * R * ((r_lo - c - 1) * (r_lo - c - 1)) +
          3 * R * ((c + 1) * R - (r_lo - c - 1) * (r_lo - c - 1)) =
          3 * R * ((c + 1) * R) := by
        rw [← Nat.mul_add]; congr 1; omega
      -- 3R(c+1)R = 3(R*R)(c+1)
      have h_assoc : 3 * R * ((c + 1) * R) = 3 * (R * R) * (c + 1) := by
        -- 3*R*((c+1)*R) = 3*(R*((c+1)*R)) = 3*((c+1)*(R*R)) = 3*(c+1)*(R*R) = (3*(R*R))*(c+1)
        suffices h : (↑(3 * R * ((c + 1) * R)) : Int) = ↑(3 * (R * R) * (c + 1)) by
          exact_mod_cast h
        push_cast
        simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      -- Final: use Nat.le_of_lt on the strict chain
      exact Nat.le_of_lt (calc
        3 * R * ((r_lo - c - 1) * (r_lo - c - 1)) +
            (r_lo - c - 1) * ((r_lo - c - 1) * (r_lo - c - 1))
          < 3 * R * ((r_lo - c - 1) * (r_lo - c - 1)) +
            3 * R * ((c + 1) * R - (r_lo - c - 1) * (r_lo - c - 1)) := by omega
        _ = 3 * R * ((c + 1) * R) := h_sum
        _ = 3 * (R * R) * (c + 1) := h_assoc)

-- ============================================================================
-- Sub-lemma E1: r_qc ≤ R_MAX (cube bound via concrete threshold)
-- ============================================================================

/-- The maximum value the composition pipeline can return.
    From 512Math.sol cbrt(): for x_norm ∈ [R_MAX³, 2^512), the algorithm returns
    exactly R_MAX. Combined with sub-lemma B (r_qc ≤ icbrt + 1), this gives
    r_qc ≤ R_MAX for ALL normalized inputs, hence r_qc³ < 2^512 = WORD_MOD². -/
private def R_MAX : Nat := 0x6597fa94f5b8f20ac16666ad0f7137bc6601d885628

set_option exponentiation.threshold 1024 in
/-- R_MAX³ < 2^512 = WORD_MOD². -/
private theorem r_max_cube_lt_wm2 : R_MAX * R_MAX * R_MAX < WORD_MOD * WORD_MOD := by
  unfold R_MAX WORD_MOD; native_decide

set_option exponentiation.threshold 1024 in
/-- R_MAX = icbrt(2^512 - 1): the largest integer whose cube < 2^512. -/
private theorem r_max_is_icbrt_wm2 :
    R_MAX * R_MAX * R_MAX ≤ WORD_MOD * WORD_MOD - 1 ∧
    WORD_MOD * WORD_MOD - 1 < (R_MAX + 1) * (R_MAX + 1) * (R_MAX + 1) := by
  unfold R_MAX WORD_MOD; constructor <;> native_decide

/-- M_TOP = icbrt((2^256-1)/4) = icbrt(2^254 - 1), the max possible m value. -/
private def M_TOP : Nat := 0x1965fea53d6e3c82b05999

set_option exponentiation.threshold 1024 in
/-- M_TOP³ ≤ 2^254 - 1 and 2^254 ≤ (M_TOP+1)³, so M_TOP = icbrt(2^254 - 1). -/
private theorem m_top_cube_bounds :
    M_TOP * M_TOP * M_TOP ≤ 2 ^ 254 - 1 ∧
    2 ^ 254 ≤ (M_TOP + 1) * (M_TOP + 1) * (M_TOP + 1) := by
  unfold M_TOP; constructor <;> native_decide

set_option exponentiation.threshold 1024 in
/-- R_MAX ≥ M_TOP * 2^86 (i.e. DELTA ≥ 0 in Nat subtraction). -/
private theorem r_max_ge_r_top : M_TOP * 2 ^ 86 ≤ R_MAX := by
  unfold M_TOP R_MAX; native_decide

set_option exponentiation.threshold 1024 in
/-- Key numerical facts for Case B (m = M_TOP):
    1. The max r_lo value is DELTA + 1
    2. At r_lo = DELTA + 1, correction ≥ 1
    3. DELTA ≥ 9 (for Case A bound) -/
private theorem r_lo_max_at_m_top :
    let R := M_TOP * 2 ^ 86
    let delta := R_MAX - R
    let res_max := 2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP
    let d := 3 * (M_TOP * M_TOP)
    -- r_lo_upper = (res_max * 2^86 + 2^86 - 1) / d
    (res_max * 2 ^ 86 + 2 ^ 86 - 1) / d ≤ delta + 1 ∧
    (delta + 1) * (delta + 1) / R ≥ 1 ∧
    9 ≤ delta := by
  unfold M_TOP R_MAX; native_decide

set_option exponentiation.threshold 1024 in
/-- For m ≥ 2^83, (3m+1) · 2^86 ≤ 27 · m · m.
    Proof: 27m² - 3m·2^86 = 3m(9m - 2^86) ≥ 3·2^83·2^83 = 3·2^166 ≥ 2^86. -/
private theorem tight_numerator_bound (m : Nat) (hm : 2 ^ 83 ≤ m) :
    (3 * m + 1) * 2 ^ 86 ≤ 27 * (m * m) := by
  -- 9m ≥ 9 · 2^83 = 2^86 + 2^83
  have h9m : 2 ^ 86 + 2 ^ 83 ≤ 9 * m := by omega
  -- So 9m - 2^86 ≥ 2^83
  have h9m_sub : 2 ^ 83 ≤ 9 * m - 2 ^ 86 := by omega
  -- 3m(9m - 2^86) ≥ 3 · 2^83 · 2^83 = 3 · 2^166
  have h_prod : 3 * 2 ^ 166 ≤ 3 * m * (9 * m - 2 ^ 86) :=
    calc 3 * 2 ^ 166
        = 3 * (2 ^ 83 * 2 ^ 83) := by rw [show (166 : Nat) = 83 + 83 from rfl, Nat.pow_add]
      _ ≤ 3 * (m * (9 * m - 2 ^ 86)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hm h9m_sub)
      _ = 3 * m * (9 * m - 2 ^ 86) := (Nat.mul_assoc 3 m _).symm
  -- 3 · 2^166 ≥ 2^86
  have h_big : (2 : Nat) ^ 86 ≤ 3 * 2 ^ 166 := by
    show 2 ^ 86 ≤ 3 * 2 ^ 166
    calc 2 ^ 86 ≤ 1 * 2 ^ 166 := by
          show 2 ^ 86 ≤ 2 ^ 166
          exact Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ 3 * 2 ^ 166 := Nat.mul_le_mul_right _ (by omega)
  -- Now: (3m+1) · 2^86 = 3m · 2^86 + 2^86 ≤ 3m · 2^86 + 3m(9m - 2^86)
  --   = 3m · (2^86 + 9m - 2^86) = 3m · 9m = 27m²
  -- But we need to handle Nat subtraction carefully.
  -- 27m² = 3m · 9m = 3m · (2^86 + (9m - 2^86))  [since 9m ≥ 2^86]
  --       = 3m · 2^86 + 3m · (9m - 2^86)
  -- 27m² = 3m · (2^86 + (9m - 2^86)) = 3m·2^86 + 3m·(9m-2^86)
  have h_split : 27 * (m * m) = 3 * m * 2 ^ 86 + 3 * m * (9 * m - 2 ^ 86) := by
    rw [← Nat.mul_add]
    -- 2^86 + (9m - 2^86) = 9m
    have h9m_eq : 2 ^ 86 + (9 * m - 2 ^ 86) = 9 * m := by omega
    rw [h9m_eq]
    -- 3m · 9m = 27 · (m·m)
    suffices h : (↑(27 * (m * m)) : Int) = ↑(3 * m * (9 * m)) by exact_mod_cast h
    push_cast
    simp only [show (27 : Int) = 3 * 9 from rfl,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  -- (3m+1)·2^86 = 3m·2^86 + 2^86
  have h_lhs : (3 * m + 1) * 2 ^ 86 = 3 * m * 2 ^ 86 + 2 ^ 86 := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  rw [h_split, h_lhs]
  exact Nat.add_le_add_left (Nat.le_trans h_big h_prod) _

/-- The composition pipeline output never exceeds R_MAX.
    Proof has two cases:
    1. m ≤ M_TOP - 1: r_qc ≤ R + r_lo < (M_TOP-1)·2^86 + 2^86 + 8 = M_TOP·2^86 + 8 ≤ R_MAX.
    2. m = M_TOP: tight numerical analysis; if r_lo ≤ DELTA then trivial,
       if r_lo = DELTA + 1 then correction ≥ 1 compensates. -/
private theorem r_qc_le_r_max (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD) :
    let w := x_hi_1 / 4
    let m := icbrt w
    let res := w - m * m * m
    let d := 3 * (m * m)
    let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
    let r_lo := (res * 2 ^ 86 + limb_hi) / d
    let R := m * 2 ^ 86
    let correction := r_lo * r_lo / R
    let r_qc := R + r_lo - correction
    r_qc ≤ R_MAX := by
  simp only
  -- ======== Step 1: Extract base case properties ========
  have hbc := model_cbrtBaseCase_evm_correct x_hi_1 hxhi_lo hxhi_hi
  have hm_lo : 2 ^ 83 ≤ icbrt (x_hi_1 / 4) := hbc.2.2.2.1
  have hm_hi : icbrt (x_hi_1 / 4) < 2 ^ 85 := hbc.2.2.2.2.1
  have hcube_le_w : icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)
      ≤ x_hi_1 / 4 := hbc.2.2.2.2.2.1
  have hres_bound : x_hi_1 / 4 - icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)
      ≤ 3 * (icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)) + 3 * icbrt (x_hi_1 / 4) :=
    hbc.2.2.2.2.2.2.1
  have hd_pos : 3 * (icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)) > 0 :=
    hbc.2.2.2.2.2.2.2.2.2.2
  -- Abbreviate
  let m := icbrt (x_hi_1 / 4)
  let w := x_hi_1 / 4
  let res := w - m * m * m
  let d := 3 * (m * m)
  let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
  let r_lo := (res * 2 ^ 86 + limb_hi) / d
  let R := m * 2 ^ 86
  let c := r_lo * r_lo / R
  -- ======== Step 2: Key bounds ========
  have hR_lo : 2 ^ 169 ≤ R :=
    calc 2 ^ 169 = 2 ^ 83 * 2 ^ 86 := by rw [← Nat.pow_add]
      _ ≤ m * 2 ^ 86 := Nat.mul_le_mul_right _ hm_lo
  have hR_pos : 0 < R := by omega
  have hlimb_bound : limb_hi < 2 ^ 86 := by
    show (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86
    have hmod4 : x_hi_1 % 4 < 4 := Nat.mod_lt _ (by omega)
    have hdiv : x_lo_1 / 2 ^ 172 < 2 ^ 84 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 172)]
      calc x_lo_1 < WORD_MOD := hxlo
        _ = 2 ^ 84 * 2 ^ 172 := by unfold WORD_MOD; rw [← Nat.pow_add]
    have : (x_hi_1 % 4) * 2 ^ 84 < 2 ^ 86 :=
      calc (x_hi_1 % 4) * 2 ^ 84 < 4 * 2 ^ 84 :=
              Nat.mul_lt_mul_of_pos_right hmod4 (Nat.two_pow_pos 84)
        _ = 2 ^ 86 := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
    omega
  -- r_qc ≤ R + r_lo (correction ≥ 0)
  have h_rqc_le : R + r_lo - c ≤ R + r_lo := Nat.sub_le _ _
  -- ======== Step 3: Case split on m < M_TOP vs m ≥ M_TOP ========
  by_cases hm_lt_top : m < M_TOP
  · -- ======== Case A: m ≤ M_TOP - 1 ========
    -- r_lo ≤ 2^86 + 8 via tight_numerator_bound
    have hr_lo_tight : r_lo ≤ 2 ^ 86 + 8 := by
      show (res * 2 ^ 86 + limb_hi) / d ≤ 2 ^ 86 + 8
      -- Suffices: numerator < (2^86 + 9) * d
      suffices h : res * 2 ^ 86 + limb_hi < (2 ^ 86 + 9) * d by
        exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hd_pos).mpr h)
      -- numerator < (3m² + 3m + 1) * 2^86
      have h_num : res * 2 ^ 86 + limb_hi < (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by
        calc res * 2 ^ 86 + limb_hi
            < res * 2 ^ 86 + 2 ^ 86 := by omega
          _ = (res + 1) * 2 ^ 86 := by rw [Nat.add_mul, Nat.one_mul]
          _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 :=
              Nat.mul_le_mul_right _ (Nat.succ_le_succ hres_bound)
      -- (2^86 + 9) * d = 2^86 * d + 9 * d = 3m² * 2^86 + 9 * 3m²
      -- (3m² + 3m + 1) * 2^86 = 3m² * 2^86 + (3m+1) * 2^86
      -- From tight_numerator_bound: (3m+1) * 2^86 ≤ 27m² = 9 * 3m² = 9 * d
      have h27 := tight_numerator_bound m hm_lo
      -- So (3m² + 3m + 1) * 2^86 ≤ 3m² * 2^86 + 9 * d = (2^86 + 9) * d
      -- 3m²·2^86 + 27m² = (2^86 + 9) · 3m² = (2^86 + 9) · d
      have h_rhs : 3 * (m * m) * 2 ^ 86 + 27 * (m * m) = (2 ^ 86 + 9) * d := by
        show 3 * (m * m) * 2 ^ 86 + 27 * (m * m) = (2 ^ 86 + 9) * (3 * (m * m))
        omega
      calc res * 2 ^ 86 + limb_hi
          < (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := h_num
        _ = 3 * (m * m) * 2 ^ 86 + (3 * m + 1) * 2 ^ 86 := by
            -- (a + b) * c = a*c + b*c
            have : (3 * (m * m) + (3 * m + 1)) * 2 ^ 86 =
                3 * (m * m) * 2 ^ 86 + (3 * m + 1) * 2 ^ 86 :=
              Nat.add_mul _ _ _
            omega
        _ ≤ 3 * (m * m) * 2 ^ 86 + 27 * (m * m) := Nat.add_le_add_left h27 _
        _ = (2 ^ 86 + 9) * d := h_rhs
    -- R ≤ (M_TOP - 1) * 2^86
    have hR_le : R ≤ (M_TOP - 1) * 2 ^ 86 :=
      Nat.mul_le_mul_right _ (by omega : m ≤ M_TOP - 1)
    -- r_qc ≤ R + r_lo ≤ (M_TOP - 1) * 2^86 + 2^86 + 8 = M_TOP * 2^86 + 8
    have h_sum : R + r_lo ≤ M_TOP * 2 ^ 86 + 8 :=
      calc R + r_lo
          ≤ (M_TOP - 1) * 2 ^ 86 + (2 ^ 86 + 8) := Nat.add_le_add hR_le hr_lo_tight
        _ = M_TOP * 2 ^ 86 + 8 := by
            rw [show M_TOP * 2 ^ 86 = (M_TOP - 1) * 2 ^ 86 + 1 * 2 ^ 86 from by omega]
    -- M_TOP * 2^86 + 8 ≤ R_MAX (since delta ≥ 9)
    have h_delta : 9 ≤ R_MAX - M_TOP * 2 ^ 86 := (r_lo_max_at_m_top).2.2
    have h_top_le : M_TOP * 2 ^ 86 + 8 ≤ R_MAX := by omega
    calc R + r_lo - c ≤ R + r_lo := h_rqc_le
      _ ≤ M_TOP * 2 ^ 86 + 8 := h_sum
      _ ≤ R_MAX := h_top_le
  · -- ======== Case B: m ≥ M_TOP, hence m = M_TOP ========
    have hm_ge : M_TOP ≤ m := by omega
    -- w < 2^254
    have hw_hi : w < 2 ^ 254 := by
      show x_hi_1 / 4 < 2 ^ 254; unfold WORD_MOD at hxhi_hi; omega
    -- (M_TOP + 1)³ > 2^254 > w, so m ≤ M_TOP
    have hm_le : m ≤ M_TOP := by
      -- If m ≥ M_TOP + 1, then m³ ≥ (M_TOP+1)³ ≥ 2^254 > w, contradicting m = icbrt(w)
      by_cases hm_eq : m ≤ M_TOP
      · exact hm_eq
      · exfalso
        have : M_TOP + 1 ≤ m := by omega
        have : (M_TOP + 1) * (M_TOP + 1) * (M_TOP + 1) ≤ m * m * m := cube_monotone this
        have : m * m * m ≤ w := hcube_le_w
        have := m_top_cube_bounds.2
        omega
    have hm_eq : m = M_TOP := Nat.le_antisymm hm_le hm_ge
    -- Substitute m = M_TOP everywhere
    -- r_lo ≤ delta + 1 from r_lo_max_at_m_top
    have h_rtop := r_lo_max_at_m_top
    let delta := R_MAX - M_TOP * 2 ^ 86
    -- Bound r_lo using res ≤ 3m² + 3m and w < 2^254
    -- res = w - m³ < 2^254 - M_TOP³ ≤ res_max  (since w ≤ 2^254 - 1)
    have hres_le : res ≤ 2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP := by
      show w - m * m * m ≤ 2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP
      rw [hm_eq]; omega
    have hd_eq : d = 3 * (M_TOP * M_TOP) := by show 3 * (m * m) = 3 * (M_TOP * M_TOP); rw [hm_eq]
    have hr_lo_le : r_lo ≤ delta + 1 := by
      show (res * 2 ^ 86 + limb_hi) / d ≤ delta + 1
      -- numerator ≤ res_max * 2^86 + 2^86 - 1
      have h_num : res * 2 ^ 86 + limb_hi ≤
          (2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP) * 2 ^ 86 + 2 ^ 86 - 1 := by
        have : limb_hi ≤ 2 ^ 86 - 1 := by omega
        calc res * 2 ^ 86 + limb_hi
            ≤ (2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP) * 2 ^ 86 + (2 ^ 86 - 1) :=
              Nat.add_le_add (Nat.mul_le_mul_right _ hres_le) this
          _ = (2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP) * 2 ^ 86 + 2 ^ 86 - 1 := by omega
      -- From h_rtop.1: (res_max * 2^86 + 2^86 - 1) / (3*(M_TOP*M_TOP)) ≤ delta + 1
      rw [hd_eq]
      exact Nat.le_trans (Nat.div_le_div_right h_num) h_rtop.1
    -- Case split: r_lo ≤ delta vs r_lo = delta + 1
    by_cases hr_lo_delta : r_lo ≤ delta
    · -- r_lo ≤ delta: r_qc ≤ R + r_lo ≤ M_TOP * 2^86 + delta = R_MAX
      have hR_eq : R = M_TOP * 2 ^ 86 := by show m * 2 ^ 86 = M_TOP * 2 ^ 86; rw [hm_eq]
      calc R + r_lo - c
          ≤ R + r_lo := h_rqc_le
        _ = M_TOP * 2 ^ 86 + r_lo := by rw [hR_eq]
        _ ≤ M_TOP * 2 ^ 86 + delta := Nat.add_le_add_left hr_lo_delta _
        _ = R_MAX := by unfold delta; omega
    · -- r_lo > delta, i.e. r_lo = delta + 1 (since r_lo ≤ delta + 1)
      have hr_lo_eq : r_lo = delta + 1 := by omega
      -- correction = r_lo² / R ≥ (delta+1)² / (M_TOP * 2^86) ≥ 1
      have hR_eq : R = M_TOP * 2 ^ 86 := by show m * 2 ^ 86 = M_TOP * 2 ^ 86; rw [hm_eq]
      have hc_ge1 : 1 ≤ c := by
        show 1 ≤ r_lo * r_lo / R
        rw [hr_lo_eq, hR_eq]
        exact h_rtop.2.1
      -- r_qc = R + r_lo - c ≤ R + (delta + 1) - 1 = R + delta = M_TOP * 2^86 + delta = R_MAX
      calc R + r_lo - c
          ≤ R + r_lo - 1 := Nat.sub_le_sub_left hc_ge1 (R + r_lo)
        _ = M_TOP * 2 ^ 86 + (delta + 1) - 1 := by rw [hR_eq, hr_lo_eq]
        _ = M_TOP * 2 ^ 86 + delta := by omega
        _ = R_MAX := by unfold delta; omega

-- ============================================================================
-- Helper: R + r_lo ≤ R_MAX + 1 (for strict cube bound when c ≥ 2)
-- ============================================================================

/-- The sum R + r_lo is at most R_MAX + 1. Combined with c ≥ 2, this gives
    r_qc = R + r_lo - c ≤ R_MAX - 1, so (r_qc + 1)³ ≤ R_MAX³ < WORD_MOD². -/
private theorem r_plus_rlo_le_rmax_succ (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD) :
    let w := x_hi_1 / 4
    let m := icbrt w
    let res := w - m * m * m
    let d := 3 * (m * m)
    let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
    let r_lo := (res * 2 ^ 86 + limb_hi) / d
    let R := m * 2 ^ 86
    R + r_lo ≤ R_MAX + 1 := by
  simp only
  have hbc := model_cbrtBaseCase_evm_correct x_hi_1 hxhi_lo hxhi_hi
  have hm_lo : 2 ^ 83 ≤ icbrt (x_hi_1 / 4) := hbc.2.2.2.1
  have hm_hi : icbrt (x_hi_1 / 4) < 2 ^ 85 := hbc.2.2.2.2.1
  have hcube_le_w : icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)
      ≤ x_hi_1 / 4 := hbc.2.2.2.2.2.1
  have hres_bound : x_hi_1 / 4 - icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)
      ≤ 3 * (icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)) + 3 * icbrt (x_hi_1 / 4) :=
    hbc.2.2.2.2.2.2.1
  have hd_pos : 3 * (icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)) > 0 :=
    hbc.2.2.2.2.2.2.2.2.2.2
  let m := icbrt (x_hi_1 / 4)
  let w := x_hi_1 / 4
  let res := w - m * m * m
  let d := 3 * (m * m)
  let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
  let r_lo := (res * 2 ^ 86 + limb_hi) / d
  let R := m * 2 ^ 86
  -- Case A: m < M_TOP → R + r_lo ≤ M_TOP*2^86 + 8 ≤ R_MAX ≤ R_MAX + 1
  -- Case B: m = M_TOP → R + r_lo ≤ M_TOP*2^86 + delta + 1 = R_MAX + 1
  by_cases hm_lt_top : m < M_TOP
  · -- Case A: reuse tight r_lo bound
    have hlimb_bound : limb_hi < 2 ^ 86 := by
      show (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86
      have : x_hi_1 % 4 < 4 := Nat.mod_lt _ (by omega)
      have : x_lo_1 / 2 ^ 172 < 2 ^ 84 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 172)]
        calc x_lo_1 < WORD_MOD := hxlo
          _ = 2 ^ 84 * 2 ^ 172 := by unfold WORD_MOD; rw [← Nat.pow_add]
      have : (x_hi_1 % 4) * 2 ^ 84 < 2 ^ 86 :=
        calc (x_hi_1 % 4) * 2 ^ 84 < 4 * 2 ^ 84 :=
                Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos 84)
          _ = 2 ^ 86 := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
      omega
    have hr_lo_tight : r_lo ≤ 2 ^ 86 + 8 := by
      show (res * 2 ^ 86 + limb_hi) / d ≤ 2 ^ 86 + 8
      suffices h : res * 2 ^ 86 + limb_hi < (2 ^ 86 + 9) * d by
        exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hd_pos).mpr h)
      have h_num : res * 2 ^ 86 + limb_hi < (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by
        calc res * 2 ^ 86 + limb_hi
            < res * 2 ^ 86 + 2 ^ 86 := by omega
          _ = (res + 1) * 2 ^ 86 := by rw [Nat.add_mul, Nat.one_mul]
          _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 :=
              Nat.mul_le_mul_right _ (Nat.succ_le_succ hres_bound)
      have h27 := tight_numerator_bound m hm_lo
      have h_rhs : 3 * (m * m) * 2 ^ 86 + 27 * (m * m) = (2 ^ 86 + 9) * d := by
        show 3 * (m * m) * 2 ^ 86 + 27 * (m * m) = (2 ^ 86 + 9) * (3 * (m * m)); omega
      calc res * 2 ^ 86 + limb_hi
          < (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := h_num
        _ = 3 * (m * m) * 2 ^ 86 + (3 * m + 1) * 2 ^ 86 := by
            have : (3 * (m * m) + (3 * m + 1)) * 2 ^ 86 =
                3 * (m * m) * 2 ^ 86 + (3 * m + 1) * 2 ^ 86 := Nat.add_mul _ _ _
            omega
        _ ≤ 3 * (m * m) * 2 ^ 86 + 27 * (m * m) := Nat.add_le_add_left h27 _
        _ = (2 ^ 86 + 9) * d := h_rhs
    have hR_le : R ≤ (M_TOP - 1) * 2 ^ 86 :=
      Nat.mul_le_mul_right _ (by omega : m ≤ M_TOP - 1)
    have h_delta : 9 ≤ R_MAX - M_TOP * 2 ^ 86 := (r_lo_max_at_m_top).2.2
    calc R + r_lo
        ≤ (M_TOP - 1) * 2 ^ 86 + (2 ^ 86 + 8) := Nat.add_le_add hR_le hr_lo_tight
      _ = M_TOP * 2 ^ 86 + 8 := by omega
      _ ≤ R_MAX := by omega
      _ ≤ R_MAX + 1 := Nat.le_succ _
  · -- Case B: m = M_TOP
    have hm_ge : M_TOP ≤ m := by omega
    have hw_hi : w < 2 ^ 254 := by show x_hi_1 / 4 < 2 ^ 254; unfold WORD_MOD at hxhi_hi; omega
    have hm_le : m ≤ M_TOP := by
      by_cases hm_eq : m ≤ M_TOP
      · exact hm_eq
      · exfalso
        have : M_TOP + 1 ≤ m := by omega
        have : (M_TOP + 1) * (M_TOP + 1) * (M_TOP + 1) ≤ m * m * m := cube_monotone this
        have : m * m * m ≤ w := hcube_le_w
        have := m_top_cube_bounds.2; omega
    have hm_eq : m = M_TOP := Nat.le_antisymm hm_le hm_ge
    have h_rtop := r_lo_max_at_m_top
    let delta := R_MAX - M_TOP * 2 ^ 86
    have hlimb_bound : limb_hi < 2 ^ 86 := by
      show (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86
      have : x_hi_1 % 4 < 4 := Nat.mod_lt _ (by omega)
      have : x_lo_1 / 2 ^ 172 < 2 ^ 84 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 172)]
        calc x_lo_1 < WORD_MOD := hxlo
          _ = 2 ^ 84 * 2 ^ 172 := by unfold WORD_MOD; rw [← Nat.pow_add]
      have : (x_hi_1 % 4) * 2 ^ 84 < 2 ^ 86 :=
        calc (x_hi_1 % 4) * 2 ^ 84 < 4 * 2 ^ 84 :=
                Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos 84)
          _ = 2 ^ 86 := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
      omega
    have hres_le : res ≤ 2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP := by
      show w - m * m * m ≤ 2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP; rw [hm_eq]; omega
    have hd_eq : d = 3 * (M_TOP * M_TOP) := by
      show 3 * (m * m) = 3 * (M_TOP * M_TOP); rw [hm_eq]
    have hr_lo_le : r_lo ≤ delta + 1 := by
      show (res * 2 ^ 86 + limb_hi) / d ≤ delta + 1
      have h_num : res * 2 ^ 86 + limb_hi ≤
          (2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP) * 2 ^ 86 + 2 ^ 86 - 1 := by
        have : limb_hi ≤ 2 ^ 86 - 1 := by omega
        calc res * 2 ^ 86 + limb_hi
            ≤ (2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP) * 2 ^ 86 + (2 ^ 86 - 1) :=
              Nat.add_le_add (Nat.mul_le_mul_right _ hres_le) this
          _ = (2 ^ 254 - 1 - M_TOP * M_TOP * M_TOP) * 2 ^ 86 + 2 ^ 86 - 1 := by omega
      rw [hd_eq]; exact Nat.le_trans (Nat.div_le_div_right h_num) h_rtop.1
    have hR_eq : R = M_TOP * 2 ^ 86 := by show m * 2 ^ 86 = M_TOP * 2 ^ 86; rw [hm_eq]
    calc R + r_lo
        = M_TOP * 2 ^ 86 + r_lo := by rw [hR_eq]
      _ ≤ M_TOP * 2 ^ 86 + (delta + 1) := Nat.add_le_add_left hr_lo_le _
      _ = R_MAX + 1 := by unfold delta; omega

-- ============================================================================
-- Sub-lemma E2: Overshoot implies not a perfect cube
-- ============================================================================

/-- When the algorithm overshoots (r_qc³ > x_norm), x_norm is not a perfect cube.
    From sub-lemmas A and B, r_qc = icbrt(x_norm) + 1 when r_qc³ > x_norm.
    If x_norm were a perfect cube s³, the Karatsuba quotient r_lo captures the
    exact linear correction and the quadratic correction c = ⌊r_lo²/R⌋ exactly
    compensates, yielding r_qc = s (no overshoot). -/

-- Helper: (t + delta)² ≥ delta * R when 3R²·delta ≤ 3Rt² + t³ (perfect cube constraint).
-- Case 1 (t² < 6R): cancel 3R from 3R²·delta < 3R(t²+2t) → R·delta < t²+2t ≤ (t+delta)².
-- Case 2 (t² ≥ 6R): multiply by 3R: 3R²·delta ≤ 3Rt² + t³ ≤ 3Rt² + 6Rt·delta ≤ 3R(t+delta)².
private theorem quad_correction_ge_delta (R t delta : Nat)
    (hR_lo : 2 ^ 169 ≤ R) (hdelta_pos : 0 < delta)
    (hcube_upper : 3 * (R * R) * delta ≤ 3 * R * (t * t) + t * t * t)
    (hcube_lower : 3 * R * (t * t) + t * t * t < 3 * (R * R) * delta + 3 * (R * R) + 2 ^ 172) :
    delta * R ≤ (t + delta) * (t + delta) := by
  have hR_pos : 0 < R := by omega
  by_cases ht_sq : t * t < 6 * R
  · -- Case 1: t² < 6R. If t = 0, hcube_upper forces delta = 0, contradiction.
    by_cases ht0 : t = 0
    · -- t = 0: 3R²·delta ≤ 0, contradiction
      exfalso
      have h1 : 0 < 3 * (R * R) * delta :=
        Nat.mul_pos (Nat.mul_pos (by omega) (Nat.mul_pos hR_pos hR_pos)) hdelta_pos
      rw [ht0, show (0 : Nat) * 0 = 0 from rfl, Nat.mul_zero, Nat.add_zero] at hcube_upper
      omega
    · -- t ≥ 1: t³ = t·t² < t·6R, so 3R²·delta < 3R(t²+2t), cancel 3R → R·delta < t²+2t
      have ht_pos : 0 < t := by omega
      have ht3_bound : t * t * t < 6 * R * t := by
        rw [show t * t * t = t * (t * t) from Nat.mul_assoc _ _ _,
            show 6 * R * t = t * (6 * R) from by
              simp only [Nat.mul_comm, Nat.mul_left_comm]]
        exact Nat.mul_lt_mul_of_pos_left ht_sq ht_pos
      -- 3R²·delta ≤ 3Rt² + t³ < 3Rt² + 6Rt = 3R(t² + 2t)
      have h_bound : 3 * (R * R) * delta < 3 * R * (t * t + 2 * t) := by
        have h6eq : 6 * R * t = 3 * R * (2 * t) := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        calc 3 * (R * R) * delta
            ≤ 3 * R * (t * t) + t * t * t := hcube_upper
          _ < 3 * R * (t * t) + 6 * R * t := by omega
          _ = 3 * R * (t * t) + 3 * R * (2 * t) := by rw [h6eq]
          _ = 3 * R * (t * t + 2 * t) := by rw [← Nat.mul_add]
      -- Cancel 3R: R·delta < t² + 2t
      have h_cancel : R * delta < t * t + 2 * t := by
        have h_assoc : 3 * (R * R) * delta = 3 * R * (R * delta) := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        rw [h_assoc] at h_bound
        exact Nat.lt_of_mul_lt_mul_left h_bound
      -- (t+delta)² = t² + 2t·delta + delta² ≥ t² + 2t ≥ R·delta + 1
      have h_sq_lb : t * t + 2 * t ≤ (t + delta) * (t + delta) := by
        rw [sq_sum_expand t delta]
        have : 2 * t ≤ 2 * t * delta := Nat.le_mul_of_pos_right _ hdelta_pos
        omega
      calc delta * R = R * delta := Nat.mul_comm _ _
        _ ≤ t * t + 2 * t := by omega
        _ ≤ (t + delta) * (t + delta) := h_sq_lb
  · -- Case 2: t² ≥ 6R. Strategy: show 3R²·delta ≤ 3R·(t+delta)² by t³ ≤ 6Rt·delta.
    have ht_sq_ge : 6 * R ≤ t * t := Nat.le_of_not_lt ht_sq
    have ht_pos : 0 < t := by
      cases Nat.eq_or_lt_of_le (Nat.zero_le t) with
      | inl h => rw [← h] at ht_sq_ge; omega
      | inr h => exact h
    -- 3R² > 2^172 (from R ≥ 2^169)
    have h3R2_gt : 2 ^ 172 ≤ 3 * (R * R) :=
      -- 2^172 ≤ 2^169 * R ≤ R * R ≤ 3*(R*R)
      Nat.le_trans
        (Nat.le_trans
          (show 2 ^ 172 ≤ 2 ^ 169 * R from
            calc 2 ^ 172 = 2 ^ 169 * 2 ^ 3 := by rw [← Nat.pow_add]
              _ ≤ 2 ^ 169 * R := Nat.mul_le_mul_left _ (by omega : 2 ^ 3 ≤ R))
          (Nat.mul_le_mul_right _ hR_lo))
        (Nat.le_mul_of_pos_left _ (by omega))
    -- t² < R·(delta+2): from 3Rt² ≤ 3Rt²+t³ < 3R²(delta+2) (since 2^172 < 3R²)
    have h_Rdelta2 : t * t < R * (delta + 2) := by
      have h_rhs : 3 * (R * R) * delta + 3 * (R * R) + 2 ^ 172 ≤
          3 * (R * R) * (delta + 2) := by
        rw [show 3 * (R * R) * (delta + 2) = 3 * (R * R) * delta + 3 * (R * R) * 2 from
          Nat.mul_add _ _ _]; omega
      have h_3Rt2 : 3 * R * (t * t) < 3 * (R * R) * (delta + 2) :=
        calc 3 * R * (t * t) ≤ 3 * R * (t * t) + t * t * t := Nat.le_add_right _ _
          _ < 3 * (R * R) * delta + 3 * (R * R) + 2 ^ 172 := hcube_lower
          _ ≤ 3 * (R * R) * (delta + 2) := h_rhs
      have h_assoc : 3 * (R * R) * (delta + 2) = 3 * R * (R * (delta + 2)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [h_assoc] at h_3Rt2
      exact Nat.lt_of_mul_lt_mul_left h_3Rt2
    -- R·delta ≥ t² - 2R (in Nat; t² ≥ 6R > 2R so no underflow concern)
    have h_Rdelta_lb : t * t - 2 * R ≤ R * delta := by
      rw [show R * (delta + 2) = R * delta + R * 2 from Nat.mul_add _ _ _] at h_Rdelta2; omega
    -- 6·R·delta ≥ t²: from 5t² ≥ 12R (via t² ≥ 6R) and R·delta ≥ t² - 2R
    have h_6Rd : t * t ≤ 6 * (R * delta) := by
      have h5t2 : 12 * R ≤ 5 * (t * t) :=
        calc 12 * R ≤ 2 * (6 * R) := by omega
          _ ≤ 2 * (t * t) := Nat.mul_le_mul_left _ ht_sq_ge
          _ ≤ 5 * (t * t) := Nat.mul_le_mul_right _ (by omega)
      calc t * t ≤ 6 * (t * t) - 12 * R := by omega
        _ ≤ 6 * (t * t - 2 * R) := by omega
        _ ≤ 6 * (R * delta) := Nat.mul_le_mul_left _ h_Rdelta_lb
    -- t³ ≤ 6Rt·delta (multiply h_6Rd by t)
    have h_t3_le : t * t * t ≤ 6 * R * delta * t := by
      rw [show t * t * t = t * (t * t) from Nat.mul_assoc _ _ _,
          show 6 * R * delta * t = t * (6 * (R * delta)) from by
            simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]]
      exact Nat.mul_le_mul_left _ h_6Rd
    -- Main: 3R²·delta ≤ 3R·(t+delta)², then cancel 3R
    suffices h_3R : 3 * (R * R) * delta ≤ 3 * R * ((t + delta) * (t + delta)) by
      -- Rewrite to 3R * (R * delta) ≤ 3R * ((t+delta)²), then cancel 3R
      have h_assoc2 : 3 * (R * R) * delta = 3 * R * (R * delta) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [h_assoc2] at h_3R
      rw [show delta * R = R * delta from Nat.mul_comm _ _]
      exact Nat.le_of_mul_le_mul_left h_3R (by omega : 0 < 3 * R)
    -- 3R²·delta ≤ 3Rt² + t³ ≤ 3Rt² + 6Rt·delta ≤ 3R(t²+2t·delta+delta²) = 3R(t+delta)²
    have h_factor : 3 * R * (t * t) + 6 * R * delta * t + 3 * R * (delta * delta) =
        3 * R * (t * t + 2 * t * delta + delta * delta) := by
      -- 6·R·delta·t = 3·R·(2·t·delta) via associativity/commutativity
      have h6 : 6 * R * delta * t = 3 * R * (2 * t * delta) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [h6, ← Nat.mul_add, ← Nat.mul_add]
    calc 3 * (R * R) * delta
        ≤ 3 * R * (t * t) + t * t * t := hcube_upper
      _ ≤ 3 * R * (t * t) + 6 * R * delta * t := by omega
      _ ≤ 3 * R * (t * t) + 6 * R * delta * t + 3 * R * (delta * delta) := Nat.le_add_right _ _
      _ = 3 * R * (t * t + 2 * t * delta + delta * delta) := h_factor
      _ = 3 * R * ((t + delta) * (t + delta)) := by congr 1; exact (sq_sum_expand t delta).symm

-- Helper: given all the bounds, show the contradiction when x_norm = s³ and r_qc > s.
-- Factored out to avoid kernel deep recursion in the main theorem.
private theorem perfect_cube_no_overshoot (s R r_lo c : Nat)
    (hR_lo : 2 ^ 169 ≤ R) (hR_pos : 0 < R)
    (hc_def : c = r_lo * r_lo / R)
    (hc_strict : c < r_lo)
    (hrqc_eq : R + r_lo - c = s + 1)
    (hs_ge_R : R ≤ s)
    (hx_lb2 : R * R * R + 3 * (R * R) * r_lo ≤ s * s * s)
    (hx_ub : s * s * s < R * R * R + 3 * (R * R) * (r_lo + 1) + 2 ^ 172) :
    False := by
  have h_cube_expand := cube_sum_expand R (s - R)
  rw [Nat.add_sub_cancel' hs_ge_R] at h_cube_expand
  have hsR_eq : s - R = r_lo - c - 1 := by
    have : R + (r_lo - c) = s + 1 := by omega
    omega
  have hdelta_eq : r_lo - (s - R) = c + 1 := by
    rw [hsR_eq]
    omega
  have hdelta_pos : 0 < r_lo - (s - R) := hdelta_eq ▸ Nat.succ_pos _
  -- hcube_upper: from hx_lb2 and cube expansion
  have hcube_upper : 3 * (R * R) * (r_lo - (s - R)) ≤
      3 * R * ((s - R) * (s - R)) + (s - R) * (s - R) * (s - R) := by
    have h_from_lb : R * R * R + 3 * (R * R) * r_lo ≤
        R * R * R + 3 * (R * R) * (s - R) + 3 * R * ((s - R) * (s - R)) +
        (s - R) * (s - R) * (s - R) := by
      calc R * R * R + 3 * (R * R) * r_lo ≤ s * s * s := hx_lb2
        _ = _ := h_cube_expand
    have h_split : 3 * (R * R) * r_lo =
        3 * (R * R) * (s - R) + 3 * (R * R) * (r_lo - (s - R)) := by
      rw [← Nat.mul_add]; congr 1; omega
    omega
  -- hcube_lower: from hx_ub and cube expansion
  have hcube_lower : 3 * R * ((s - R) * (s - R)) + (s - R) * (s - R) * (s - R) <
      3 * (R * R) * (r_lo - (s - R)) + 3 * (R * R) + 2 ^ 172 := by
    have h_from_ub : R * R * R + 3 * (R * R) * (s - R) +
        3 * R * ((s - R) * (s - R)) + (s - R) * (s - R) * (s - R) <
        R * R * R + 3 * (R * R) * (r_lo + 1) + 2 ^ 172 := by
      calc R * R * R + 3 * (R * R) * (s - R) +
            3 * R * ((s - R) * (s - R)) + (s - R) * (s - R) * (s - R)
          = s * s * s := h_cube_expand.symm
        _ < R * R * R + 3 * (R * R) * (r_lo + 1) + 2 ^ 172 := hx_ub
    have h_rlo_split : 3 * (R * R) * (r_lo + 1) =
        3 * (R * R) * (s - R) + 3 * (R * R) * (r_lo - (s - R)) + 3 * (R * R) := by
      have : r_lo + 1 = (s - R) + (r_lo - (s - R)) + 1 := by omega
      rw [this, show (s - R) + (r_lo - (s - R)) + 1 =
        (s - R) + ((r_lo - (s - R)) + 1) from by omega]
      simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    rw [h_rlo_split] at h_from_ub
    omega
  have h_qc := quad_correction_ge_delta R (s - R) (r_lo - (s - R))
    hR_lo hdelta_pos hcube_upper hcube_lower
  rw [show s - R + (r_lo - (s - R)) = r_lo from by omega] at h_qc
  have hc_ge_delta : r_lo - (s - R) ≤ c :=
    hc_def ▸ (Nat.le_div_iff_mul_le hR_pos).mpr h_qc
  -- delta = c + 1 ≤ c: contradiction
  omega

set_option exponentiation.threshold 1024 in
private theorem r_qc_no_overshoot_on_cubes (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD) :
    let w := x_hi_1 / 4
    let m := icbrt w
    let res := w - m * m * m
    let d := 3 * (m * m)
    let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
    let r_lo := (res * 2 ^ 86 + limb_hi) / d
    let R := m * 2 ^ 86
    let correction := r_lo * r_lo / R
    let r_qc := R + r_lo - correction
    let x_norm := x_hi_1 * 2 ^ 256 + x_lo_1
    r_qc * r_qc * r_qc > x_norm →
      icbrt x_norm * icbrt x_norm * icbrt x_norm < x_norm := by
  simp only
  -- ======== Step 1: Extract base case properties ========
  have hbc := model_cbrtBaseCase_evm_correct x_hi_1 hxhi_lo hxhi_hi
  have hm_lo : 2 ^ 83 ≤ icbrt (x_hi_1 / 4) := hbc.2.2.2.1
  have hcube_le_w : icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)
      ≤ x_hi_1 / 4 := hbc.2.2.2.2.2.1
  have hres_bound : x_hi_1 / 4 - icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)
      ≤ 3 * (icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)) + 3 * icbrt (x_hi_1 / 4) :=
    hbc.2.2.2.2.2.2.1
  have hd_pos : 3 * (icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)) > 0 :=
    hbc.2.2.2.2.2.2.2.2.2.2
  -- Abbreviate
  let m := icbrt (x_hi_1 / 4)
  let w := x_hi_1 / 4
  let res := w - m * m * m
  let d := 3 * (m * m)
  let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
  let r_lo := (res * 2 ^ 86 + limb_hi) / d
  let R := m * 2 ^ 86
  let c := r_lo * r_lo / R
  let rem_kq := (res * 2 ^ 86 + limb_hi) % d
  let c_tail := x_lo_1 % 2 ^ 172
  -- ======== Step 2: Key bounds (same as sub-lemma B) ========
  have hR_lo : 2 ^ 169 ≤ R :=
    calc 2 ^ 169 = 2 ^ 83 * 2 ^ 86 := by rw [← Nat.pow_add]
      _ ≤ m * 2 ^ 86 := Nat.mul_le_mul_right _ hm_lo
  have hR_pos : 0 < R := by omega
  have hlimb_bound : limb_hi < 2 ^ 86 := by
    show (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86
    have hmod4 : x_hi_1 % 4 < 4 := Nat.mod_lt _ (by omega)
    have hdiv : x_lo_1 / 2 ^ 172 < 2 ^ 84 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 172)]
      calc x_lo_1 < WORD_MOD := hxlo
        _ = 2 ^ 84 * 2 ^ 172 := by unfold WORD_MOD; rw [← Nat.pow_add]
    have : (x_hi_1 % 4) * 2 ^ 84 < 2 ^ 86 :=
      calc (x_hi_1 % 4) * 2 ^ 84 < 4 * 2 ^ 84 :=
              Nat.mul_lt_mul_of_pos_right hmod4 (Nat.two_pow_pos 84)
        _ = 2 ^ 86 := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
    omega
  have hr_lo_bound : r_lo < 2 ^ 87 := by
    show (res * 2 ^ 86 + limb_hi) / d < 2 ^ 87
    rw [Nat.div_lt_iff_lt_mul hd_pos]
    have h2m : 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
    calc res * 2 ^ 86 + limb_hi
        < (res + 1) * 2 ^ 86 := by omega
      _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by
          apply Nat.mul_le_mul_right; exact Nat.succ_le_succ hres_bound
      _ ≤ (2 * (3 * (m * m))) * 2 ^ 86 := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ 87 * (3 * (m * m)) := by
          rw [show (2 : Nat) ^ 87 = 2 * 2 ^ 86 from by
            rw [show (87 : Nat) = 1 + 86 from rfl, Nat.pow_add]]; omega
  have hrem_lt : rem_kq < d := Nat.mod_lt _ hd_pos
  have hctail_lt : c_tail < 2 ^ 172 := Nat.mod_lt _ (Nat.two_pow_pos 172)
  -- ======== Step 3: x_norm decomposition ========
  have hx_decomp := x_norm_decomp x_hi_1 x_lo_1 (m * m * m) hcube_le_w
  have hn_full := Nat.div_add_mod (res * 2 ^ 86 + limb_hi) d
  have h_num_eq : (res * 2 ^ 86 + limb_hi) = d * r_lo + rem_kq := hn_full.symm
  have h_num_mul : (d * r_lo + rem_kq) * 2 ^ 172 = d * r_lo * 2 ^ 172 + rem_kq * 2 ^ 172 :=
    Nat.add_mul _ _ _
  have hR3 := R_cube_factor m
  have hd_eq_3R2 := d_pow172_eq_3R_sq m
  have hrem_ub : rem_kq * 2 ^ 172 + c_tail < d * 2 ^ 172 + 2 ^ 172 := by
    have := Nat.mul_lt_mul_of_pos_right hrem_lt (Nat.two_pow_pos 172)
    omega
  -- x_norm ≥ R³ + 3R²·r_lo (lower bound, same as sub-lemma B)
  have hx_lb : m * m * m * 2 ^ 258 + d * r_lo * 2 ^ 172 ≤
      x_hi_1 * 2 ^ 256 + x_lo_1 := by
    rw [hx_decomp]
    rw [show ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) = d * r_lo + rem_kq from h_num_eq]
    rw [h_num_mul]
    omega
  have hx_lb2 : R * R * R + 3 * (R * R) * r_lo ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := by
    calc R * R * R + 3 * (R * R) * r_lo
        = m * m * m * 2 ^ 258 + 3 * (m * m) * r_lo * 2 ^ 172 := by
          rw [← hR3]
          show R * R * R + 3 * (R * R) * r_lo =
            R * R * R + 3 * (m * m) * r_lo * 2 ^ 172
          rw [← hd_eq_3R2]
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ = m * m * m * 2 ^ 258 + d * r_lo * 2 ^ 172 := by rfl
      _ ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := hx_lb
  -- x_norm < R³ + 3R²·(r_lo + 1) + 2^172
  have hx_ub : x_hi_1 * 2 ^ 256 + x_lo_1 <
      R * R * R + 3 * (R * R) * (r_lo + 1) + 2 ^ 172 := by
    have hx_ub_raw : x_hi_1 * 2 ^ 256 + x_lo_1 <
        m * m * m * 2 ^ 258 + d * (r_lo + 1) * 2 ^ 172 + 2 ^ 172 := by
      rw [hx_decomp]
      rw [show ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
          (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) = d * r_lo + rem_kq from h_num_eq]
      rw [h_num_mul]
      have : d * (r_lo + 1) * 2 ^ 172 = d * r_lo * 2 ^ 172 + d * 2 ^ 172 := by
        rw [show d * (r_lo + 1) = d * r_lo + d * 1 from Nat.mul_add _ _ _, Nat.mul_one,
            Nat.add_mul]
      exact by omega
    calc x_hi_1 * 2 ^ 256 + x_lo_1
        < m * m * m * 2 ^ 258 + d * (r_lo + 1) * 2 ^ 172 + 2 ^ 172 := hx_ub_raw
      _ = R * R * R + 3 * (R * R) * (r_lo + 1) + 2 ^ 172 := by
          have hdr1 : d * (r_lo + 1) * 2 ^ 172 = 3 * (R * R) * (r_lo + 1) := by
            show 3 * (m * m) * (r_lo + 1) * 2 ^ 172 = 3 * (R * R) * (r_lo + 1)
            rw [← hd_eq_3R2]
            simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          rw [← hR3, hdr1]
  -- ======== Step 4: Main proof by contradiction ========
  intro h_over
  let s := icbrt (x_hi_1 * 2 ^ 256 + x_lo_1)
  have hcube_le := icbrt_cube_le (x_hi_1 * 2 ^ 256 + x_lo_1)
  have hsucc_gt := icbrt_lt_succ_cube (x_hi_1 * 2 ^ 256 + x_lo_1)
  by_cases h_not_perf : s * s * s < x_hi_1 * 2 ^ 256 + x_lo_1
  · exact h_not_perf
  · -- Perfect cube case: derive contradiction via perfect_cube_no_overshoot
    exfalso
    have h_perf : s * s * s = x_hi_1 * 2 ^ 256 + x_lo_1 :=
      Nat.le_antisymm hcube_le (Nat.not_lt.mp h_not_perf)
    have hB := r_qc_pred_cube_le x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
    simp only at hB
    have hrqc_gt_s : s < R + r_lo - c := by
      by_cases h : s < R + r_lo - c
      · exact h
      · exfalso; have h1 := cube_monotone (Nat.not_lt.mp h)
        rw [h_perf] at h1; exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h_over h1)
    have hrqc1_le_s : R + r_lo - c - 1 ≤ s := by
      -- If s < r_qc - 1, then (s+1)³ ≤ (r_qc-1)³ ≤ x_norm = s³,
      -- contradicting hsucc_gt: x_norm < (s+1)³.
      by_cases h_gt : s < R + r_lo - c - 1
      · exfalso
        have h1 := cube_monotone (show s + 1 ≤ R + r_lo - c - 1 from by omega)
        -- h1 and hB are both about the expanded form, so Nat.le_trans works
        have h2 := Nat.le_trans h1 hB
        -- h2 : (s+1)³ ≤ x_norm. But hsucc_gt : x_norm < (s+1)³.
        exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hsucc_gt h2)
      · exact Nat.not_lt.mp h_gt
    have hrqc_eq : R + r_lo - c = s + 1 := Nat.le_antisymm (by omega) (by omega)
    have hr_lo_pos : 0 < r_lo := by
      cases Nat.eq_or_lt_of_le (Nat.zero_le r_lo) with
      | inr h => exact h
      | inl h =>
        exfalso
        have hrl0 : r_lo = 0 := h.symm
        have hc0 : c = 0 := by
          rw [show c = r_lo * r_lo / R from rfl, hrl0]
          simp
        -- s + 1 = R, so hsucc_gt: x_norm < R³. But hx_lb2: R³ ≤ x_norm.
        rw [hrl0, hc0] at hrqc_eq
        have : R * R * R ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := by
          calc R * R * R ≤ R * R * R + 3 * (R * R) * 0 := by omega
            _ = R * R * R + 3 * (R * R) * r_lo := by rw [hrl0]
            _ ≤ _ := hx_lb2
        rw [← h_perf] at this
        have : s + 1 = R := by omega
        have : x_hi_1 * 2 ^ 256 + x_lo_1 < (s + 1) * (s + 1) * (s + 1) := hsucc_gt
        rw [‹s + 1 = R›] at this
        omega
    have hc_strict : c < r_lo :=
      (Nat.div_lt_iff_lt_mul hR_pos).mpr
        (Nat.mul_lt_mul_of_pos_left (by omega : r_lo < R) hr_lo_pos)
    have hs_ge_R : R ≤ s := by omega
    exact perfect_cube_no_overshoot s R r_lo c hR_lo hR_pos rfl hc_strict
      hrqc_eq hs_ge_R (h_perf ▸ hx_lb2) (h_perf ▸ hx_ub)

-- ============================================================================
-- Combined: r_qc_properties from sub-lemmas A, B, E
-- ============================================================================

/-- The quadratic-corrected result satisfies within-1-ulp, cube bound, and
    overshoot properties. Composed from sub-lemmas A, B, E1 (r_qc ≤ R_MAX),
    and E2 (overshoot → not perfect cube). -/
private theorem r_qc_properties (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD) :
    let w := x_hi_1 / 4
    let m := icbrt w
    let res := w - m * m * m
    let d := 3 * (m * m)
    let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
    let r_lo := (res * 2 ^ 86 + limb_hi) / d
    let R := m * 2 ^ 86
    let correction := r_lo * r_lo / R
    let r_qc := R + r_lo - correction
    let x_norm := x_hi_1 * 2 ^ 256 + x_lo_1
    icbrt x_norm ≤ r_qc + 1 ∧ r_qc ≤ icbrt x_norm + 1 ∧
    r_qc * r_qc * r_qc < WORD_MOD * WORD_MOD ∧
    (r_qc * r_qc * r_qc > x_norm →
      icbrt x_norm * icbrt x_norm * icbrt x_norm < x_norm) := by
  simp only
  -- Sub-lemmas (simp only inlines the let-bindings, matching the goal)
  have hA := r_qc_succ2_cube_gt x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  have hB := r_qc_pred_cube_le x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  have hE1 := r_qc_le_r_max x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  have hE2 := r_qc_no_overshoot_on_cubes x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  simp only at hA hB hE1 hE2
  have hcube_le := icbrt_cube_le (x_hi_1 * 2 ^ 256 + x_lo_1)
  have hsucc_gt := icbrt_lt_succ_cube (x_hi_1 * 2 ^ 256 + x_lo_1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- [1] icbrt(x_norm) ≤ r_qc + 1: if r_qc + 1 < icbrt then (r_qc+2)³ ≤ icbrt³ ≤ x_norm,
    --     contradicting hA: x_norm < (r_qc+2)³.
    exact Nat.not_lt.mp fun h =>
      absurd hA (Nat.not_lt.mpr (Nat.le_trans (cube_monotone h) hcube_le))
  · -- [2] r_qc ≤ icbrt(x_norm) + 1: if icbrt+1 < r_qc then (icbrt+1)³ ≤ (r_qc-1)³ ≤ x_norm,
    --     contradicting hsucc_gt: x_norm < (icbrt+1)³.
    exact Nat.not_lt.mp fun h =>
      absurd hsucc_gt
        (Nat.not_lt.mpr (Nat.le_trans (cube_monotone (Nat.le_sub_one_of_lt h)) hB))
  · -- [3] r_qc³ < WORD_MOD²: r_qc ≤ R_MAX (E1), so r_qc³ ≤ R_MAX³ < WORD_MOD² (native_decide).
    exact Nat.lt_of_le_of_lt (cube_monotone hE1) r_max_cube_lt_wm2
  · -- [4] r_qc³ > x_norm → icbrt³ < x_norm: from E2.
    exact hE2

-- ============================================================================
-- Range bounds helper
-- ============================================================================

/-- r_qc < 2^172 (and hence < WORD_MOD). -/
private theorem r_qc_lt_pow172 (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD) :
    let w := x_hi_1 / 4
    let m := icbrt w
    let res := w - m * m * m
    let d := 3 * (m * m)
    let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
    let r_lo := (res * 2 ^ 86 + limb_hi) / d
    let R := m * 2 ^ 86
    let correction := r_lo * r_lo / R
    let r_qc := R + r_lo - correction
    r_qc < 2 ^ 172 := by
  simp only
  -- Get base case properties
  have hbc := model_cbrtBaseCase_evm_correct x_hi_1 hxhi_lo hxhi_hi
  have hm_lo : 2 ^ 83 ≤ icbrt (x_hi_1 / 4) := hbc.2.2.2.1
  have hm_hi : icbrt (x_hi_1 / 4) < 2 ^ 85 := hbc.2.2.2.2.1
  have hres_bound : x_hi_1 / 4 - icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)
      ≤ 3 * (icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)) + 3 * icbrt (x_hi_1 / 4) :=
    hbc.2.2.2.2.2.2.1
  have hd_pos : 3 * (icbrt (x_hi_1 / 4) * icbrt (x_hi_1 / 4)) > 0 := hbc.2.2.2.2.2.2.2.2.2.2
  -- Abbreviate
  let m := icbrt (x_hi_1 / 4)
  let res := x_hi_1 / 4 - m * m * m
  let d := 3 * (m * m)
  let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
  let r_lo := (res * 2 ^ 86 + limb_hi) / d
  -- R < 2^171
  have hR_lt : m * 2 ^ 86 < 2 ^ 171 :=
    calc m * 2 ^ 86
        < 2 ^ 85 * 2 ^ 86 := Nat.mul_lt_mul_of_pos_right hm_hi (Nat.two_pow_pos 86)
      _ = 2 ^ 171 := by rw [← Nat.pow_add]
  -- limb_hi < 2^86
  have hlimb_bound : limb_hi < 2 ^ 86 := by
    show (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86
    have hmod4 : x_hi_1 % 4 < 4 := Nat.mod_lt _ (by omega)
    have hdiv : x_lo_1 / 2 ^ 172 < 2 ^ 84 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 172)]
      calc x_lo_1 < WORD_MOD := hxlo
        _ = 2 ^ 84 * 2 ^ 172 := by unfold WORD_MOD; rw [← Nat.pow_add]
    have hprod : (x_hi_1 % 4) * 2 ^ 84 < 2 ^ 86 :=
      calc (x_hi_1 % 4) * 2 ^ 84 < 4 * 2 ^ 84 :=
              Nat.mul_lt_mul_of_pos_right hmod4 (Nat.two_pow_pos 84)
        _ = 2 ^ 86 := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
    omega
  -- r_lo < 2^87
  have hr_lo_bound : r_lo < 2 ^ 87 := by
    show (res * 2 ^ 86 + limb_hi) / d < 2 ^ 87
    rw [Nat.div_lt_iff_lt_mul hd_pos]
    -- 3m² + 3m + 1 ≤ 2*(3m²) = 6m²  needs  3m + 1 ≤ 3m²  needs  m + 1/3 ≤ m²
    -- From m ≥ 2: m² ≥ 2m ≥ m + m ≥ m + 2 > m + 1/3
    have h2m : 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
    have h6m2 : 3 * (m * m) + 3 * m + 1 ≤ 2 * (3 * (m * m)) := by omega
    calc res * 2 ^ 86 + limb_hi
        < (res + 1) * 2 ^ 86 := by omega
      _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by
          apply Nat.mul_le_mul_right
          show res + 1 ≤ 3 * (m * m) + 3 * m + 1
          exact Nat.succ_le_succ hres_bound
      _ ≤ (2 * (3 * (m * m))) * 2 ^ 86 := Nat.mul_le_mul_right _ h6m2
      _ = 2 ^ 87 * (3 * (m * m)) := by
          -- 2 * (3*(m*m)) * 2^86 = (2*2^86) * (3*(m*m)) = 2^87 * d
          have h287 : (2 : Nat) ^ 87 = 2 * 2 ^ 86 := by
            rw [show (87 : Nat) = 1 + 86 from rfl, Nat.pow_add]
          omega
  -- r_qc ≤ R + r_lo < 2^171 + 2^87 < 2^172
  show m * 2 ^ 86 + r_lo - r_lo * r_lo / (m * 2 ^ 86) < 2 ^ 172
  have hsub : m * 2 ^ 86 + r_lo - r_lo * r_lo / (m * 2 ^ 86) ≤ m * 2 ^ 86 + r_lo :=
    Nat.sub_le _ _
  have h2172 : (2 : Nat) ^ 172 = 2 * 2 ^ 171 := by
    rw [show (172 : Nat) = 1 + 171 from rfl, Nat.pow_add]
  omega

-- ============================================================================
-- Undershoot check helper lemmas
-- ============================================================================

/-- The mask constant 77371252455336267181195263 equals 2^86 - 1. -/
private theorem mask_86_eq : 77371252455336267181195263 = 2 ^ 86 - 1 := by native_decide

/-- evmAnd with the 86-bit mask extracts the low 86 bits (mod 2^86). -/
private theorem evmAnd_mask86_eq_mod (x : Nat) (hx : x < WORD_MOD) :
    evmAnd x 77371252455336267181195263 = x % 2 ^ 86 := by
  have hmask_wm : (77371252455336267181195263 : Nat) < WORD_MOD := by
    unfold WORD_MOD; omega
  rw [evmAnd_eq' x _ hx hmask_wm, mask_86_eq]
  exact Nat.and_two_pow_sub_one_eq_mod x 86

/-- If a ||| (b &&& c) = 1 with all values ≤ 1, then a = 1 ∨ (b = 1 ∧ c = 1). -/
private theorem or_and_eq_one_cases (a b c : Nat) (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1)
    (h : a ||| (b &&& c) = 1) : a = 1 ∨ (b = 1 ∧ c = 1) := by
  have : a = 0 ∨ a = 1 := by omega
  have : b = 0 ∨ b = 1 := by omega
  have : c = 0 ∨ c = 1 := by omega
  rcases ‹a = 0 ∨ a = 1› with rfl | rfl
  · rcases ‹b = 0 ∨ b = 1› with rfl | rfl <;>
    rcases ‹c = 0 ∨ c = 1› with rfl | rfl <;> simp_all
  · left; rfl

-- ============================================================================
-- Undershoot algebraic sub-lemmas
-- ============================================================================

/-- If eps3 < rem and R ≤ 2^172, then eps3 * R ≤ rem * 2^172. -/
private theorem eps3_lt_rem_implies_prod_le (eps3 rem R : Nat)
    (hR_le : R ≤ 2 ^ 172)
    (h_lt : eps3 < rem) :
    eps3 * R ≤ rem * 2 ^ 172 :=
  Nat.le_trans
    (Nat.mul_le_mul_right _ (Nat.le_of_lt h_lt))
    (Nat.mul_le_mul_left _ hR_le)

/-- If a/2^86 < b/2^86 then a < b. -/
private theorem div_lt_implies_lt (a b : Nat)
    (h : a / 2 ^ 86 < b / 2 ^ 86) : a < b := by
  have h1 : (a / 2 ^ 86 + 1) * 2 ^ 86 ≤ b := by
    calc (a / 2 ^ 86 + 1) * 2 ^ 86
        ≤ (b / 2 ^ 86) * 2 ^ 86 := Nat.mul_le_mul_right _ (by omega)
      _ ≤ b := by
          have := Nat.div_mul_le_self b (2 ^ 86)
          omega
  have h2 : a < (a / 2 ^ 86 + 1) * 2 ^ 86 := by
    have := Nat.div_add_mod a (2 ^ 86)
    have := Nat.mod_lt a (Nat.two_pow_pos 86)
    omega
  omega

/-- Exact split-limb comparison implies the product inequality.
    When a/2^86 = b/2^86 and (a%2^86)*m < (b%2^86)*2^86 and m ≤ 2^86,
    then a*(m*2^86) ≤ b*2^172.
    Proof: decompose a = 2^86*h + a_lo, b = 2^86*h + b_lo (same h).
    First terms bounded by m ≤ 2^86, second terms by the comparison. -/
private theorem split_limb_implies_prod_le (a b m : Nat)
    (hm_le : m ≤ 2 ^ 86)
    (h_eq : a / 2 ^ 86 = b / 2 ^ 86)
    (h_lo : (a % 2 ^ 86) * m < (b % 2 ^ 86) * 2 ^ 86) :
    a * (m * 2 ^ 86) ≤ b * 2 ^ 172 := by
  have hda := Nat.div_add_mod a (2 ^ 86)  -- 2^86 * (a/2^86) + a%2^86 = a
  have hdb := Nat.div_add_mod b (2 ^ 86)  -- 2^86 * (b/2^86) + b%2^86 = b
  have h2172 : (2 : Nat) ^ 172 = 2 ^ 86 * 2 ^ 86 := by
    rw [show (172 : Nat) = 86 + 86 from rfl, Nat.pow_add]
  rw [← hda, ← hdb, h_eq, h2172]
  rw [Nat.add_mul, Nat.add_mul]
  apply Nat.add_le_add
  · -- 2^86*h*(m*2^86) ≤ 2^86*h*(2^86*2^86) since m ≤ 2^86
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hm_le)
  · -- a%2^86*(m*2^86) ≤ b%2^86*(2^86*2^86)
    apply Nat.le_of_lt
    rw [show a % 2 ^ 86 * (m * 2 ^ 86) = (a % 2 ^ 86 * m) * 2 ^ 86 from by
          simp [Nat.mul_assoc, Nat.mul_comm m, Nat.mul_left_comm]]
    rw [show b % 2 ^ 86 * (2 ^ 86 * 2 ^ 86) = (b % 2 ^ 86 * 2 ^ 86) * 2 ^ 86 from by
          simp [Nat.mul_assoc]]
    exact Nat.mul_lt_mul_of_pos_right h_lo (Nat.two_pow_pos 86)

-- ============================================================================
-- Undershoot check algebraic consequence
-- ============================================================================

/-- When the QC model returns r_qc + 1 (undershoot correction), the split-limb
    comparison implies nat_rem * 2^172 > 3 * R * ε where R = m * 2^86 and
    ε = r_lo² mod R.  This is the key inequality making the x_norm decomposition
    positive: x_norm - r_qc³ = 3Rc(2r_lo-c) + (rem*2^172 - 3Rε) + c_tail - t³,
    and with this inequality, the (rem*2^172 - 3Rε) term is non-negative. -/
private theorem undershoot_implies_rem_gt_3Reps
    (m nat_r_lo nat_rem : Nat)
    (hm_wm : m < WORD_MOD) (hr_lo_wm : nat_r_lo < WORD_MOD) (hrem_wm : nat_rem < WORD_MOD)
    (hm_pos : 2 ≤ m) (hm_hi : m < 2 ^ 85)
    (hr_lo_bound : nat_r_lo < 2 ^ 87)
    (hc_gt1 : nat_r_lo * nat_r_lo / (m * 2 ^ 86) > 1)
    (hr1_eq : model_cbrtQuadraticCorrection_evm m nat_r_lo nat_rem =
        m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86) + 1) :
    nat_r_lo * nat_r_lo % (m * 2 ^ 86) * 3 * (m * 2 ^ 86) ≤
        nat_rem * 2 ^ 172 := by
  -- ======== Bounds setup (same as QC bridge proof) ========
  have hR_ge : 2 ^ 87 ≤ m * 2 ^ 86 :=
    calc 2 ^ 87 = 2 * 2 ^ 86 := by
          rw [show (87 : Nat) = 1 + 86 from rfl, Nat.pow_add]
      _ ≤ m * 2 ^ 86 := Nat.mul_le_mul_right _ hm_pos
  have hR_lt : m * 2 ^ 86 < 2 ^ 171 :=
    calc m * 2 ^ 86
        < 2 ^ 85 * 2 ^ 86 := Nat.mul_lt_mul_of_pos_right hm_hi (Nat.two_pow_pos 86)
      _ = 2 ^ 171 := by rw [← Nat.pow_add]
  have hR_wm : m * 2 ^ 86 < WORD_MOD := by unfold WORD_MOD; omega
  have hR_pos : 0 < m * 2 ^ 86 := by omega
  have hr_lo_sq : nat_r_lo * nat_r_lo < 2 ^ 174 := by
    cases Nat.eq_or_lt_of_le (Nat.zero_le nat_r_lo) with
    | inl h => rw [← h]; simp
    | inr h =>
      calc nat_r_lo * nat_r_lo
          < nat_r_lo * 2 ^ 87 := Nat.mul_lt_mul_of_pos_left hr_lo_bound h
        _ ≤ 2 ^ 87 * 2 ^ 87 := Nat.mul_le_mul_right _ (Nat.le_of_lt hr_lo_bound)
        _ = 2 ^ 174 := by rw [← Nat.pow_add]
  have hr_lo_sq_wm : nat_r_lo * nat_r_lo < WORD_MOD := by unfold WORD_MOD; omega
  have hR_gt_rlo : nat_r_lo < m * 2 ^ 86 := by omega
  have hc_le : nat_r_lo * nat_r_lo / (m * 2 ^ 86) ≤ nat_r_lo := by
    cases Nat.eq_or_lt_of_le (Nat.zero_le nat_r_lo) with
    | inl h => rw [← h]; simp
    | inr h =>
      exact Nat.le_of_lt ((Nat.div_lt_iff_lt_mul hR_pos).mpr
        (Nat.mul_lt_mul_of_pos_left hR_gt_rlo h))
  have hcR_le : (nat_r_lo * nat_r_lo / (m * 2 ^ 86)) * (m * 2 ^ 86) ≤ nat_r_lo * nat_r_lo :=
    Nat.div_mul_le_self _ _
  let c := nat_r_lo * nat_r_lo / (m * 2 ^ 86)
  have hc_wm : c < WORD_MOD := Nat.lt_of_le_of_lt hc_le hr_lo_wm
  have hcR_wm : c * (m * 2 ^ 86) < WORD_MOD :=
    Nat.lt_of_le_of_lt hcR_le hr_lo_sq_wm
  -- ======== EVM-to-Nat reduction lemmas ========
  have hR_eq : evmShl (evmAnd (evmAnd 86 255) 255) m = m * 2 ^ 86 := by
    rw [qc_const_86, evmShl_eq' 86 m (by omega) hm_wm]
    exact Nat.mod_eq_of_lt hR_wm
  have hSq_eq : evmMul nat_r_lo nat_r_lo = nat_r_lo * nat_r_lo := by
    rw [evmMul_eq' nat_r_lo nat_r_lo hr_lo_wm hr_lo_wm]; exact Nat.mod_eq_of_lt hr_lo_sq_wm
  have hC_eq : evmDiv (nat_r_lo * nat_r_lo) (m * 2 ^ 86) = c :=
    evmDiv_eq' _ _ hr_lo_sq_wm hR_pos hR_wm
  have hCR_eq : evmMul c (m * 2 ^ 86) = c * (m * 2 ^ 86) := by
    rw [evmMul_eq' c _ hc_wm hR_wm]; exact Nat.mod_eq_of_lt hcR_wm
  have hResid_eq : evmSub (nat_r_lo * nat_r_lo) (c * (m * 2 ^ 86)) =
      nat_r_lo * nat_r_lo % (m * 2 ^ 86) := by
    rw [evmSub_eq_of_le _ _ hr_lo_sq_wm hcR_le,
        show c * (m * 2 ^ 86) = (m * 2 ^ 86) * c from Nat.mul_comm _ _]
    have hdm := Nat.div_add_mod (nat_r_lo * nat_r_lo) (m * 2 ^ 86)
    rw [Nat.add_comm] at hdm
    exact Nat.sub_eq_of_eq_add hdm.symm
  have hmod_lt : nat_r_lo * nat_r_lo % (m * 2 ^ 86) < WORD_MOD :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hR_pos) (by unfold WORD_MOD; omega)
  have heps3_wm : (nat_r_lo * nat_r_lo % (m * 2 ^ 86)) * 3 < WORD_MOD := by
    calc (nat_r_lo * nat_r_lo % (m * 2 ^ 86)) * 3
        < (m * 2 ^ 86) * 3 := Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ hR_pos) (by omega)
      _ < 2 ^ 171 * 3 := Nat.mul_lt_mul_of_pos_right hR_lt (by omega)
      _ < WORD_MOD := by unfold WORD_MOD; omega
  have hEps3_eq : evmMul (nat_r_lo * nat_r_lo % (m * 2 ^ 86)) 3 =
      (nat_r_lo * nat_r_lo % (m * 2 ^ 86)) * 3 := by
    rw [evmMul_eq' _ 3 hmod_lt (by unfold WORD_MOD; omega)]
    exact Nat.mod_eq_of_lt heps3_wm
  have hSub_eq : evmSub nat_r_lo c = nat_r_lo - c :=
    evmSub_eq_of_le _ _ hr_lo_wm hc_le
  have hGt_eq : evmGt c 1 = if c > 1 then 1 else 0 :=
    evmGt_eq' c 1 hc_wm (by unfold WORD_MOD; omega)
  -- ======== Abbreviations for eps3 ========
  let eps3 := (nat_r_lo * nat_r_lo % (m * 2 ^ 86)) * 3
  -- eps3 < WORD_MOD (carry through for omega)
  have heps3_wm' : eps3 < WORD_MOD := heps3_wm
  -- ======== Unfold model in hr1_eq and simplify ========
  unfold model_cbrtQuadraticCorrection_evm at hr1_eq
  simp only [u256_id' m hm_wm, u256_id' nat_r_lo hr_lo_wm, u256_id' nat_rem hrem_wm,
             hR_eq, hSq_eq, hC_eq, hCR_eq, hResid_eq, hEps3_eq, hSub_eq, hGt_eq] at hr1_eq
  -- Now hr1_eq is about the if-then-else on c > 1
  rw [if_pos hc_gt1] at hr1_eq
  -- The if branch: evmAdd (nat_r_lo - c) (check) where check is the undershoot OR expression
  -- Since c > 1, the inner if is also taken
  rw [if_pos (show (1 : Nat) ≠ 0 from by omega)] at hr1_eq
  -- ======== Reduce the check sub-expressions ========
  -- eps3 / 2^86 and rem / 2^86 (the high parts)
  have hShr_eps3 : evmShr (evmAnd (evmAnd 86 255) 255) eps3 = eps3 / 2 ^ 86 := by
    rw [qc_const_86, evmShr_eq' 86 eps3 (by omega) heps3_wm']
  have hShr_rem : evmShr (evmAnd (evmAnd 86 255) 255) nat_rem = nat_rem / 2 ^ 86 := by
    rw [qc_const_86, evmShr_eq' 86 nat_rem (by omega) hrem_wm]
  have heps3_hi_wm : eps3 / 2 ^ 86 < WORD_MOD :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) heps3_wm'
  have hrem_hi_wm : nat_rem / 2 ^ 86 < WORD_MOD := by
    unfold WORD_MOD; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hrem_wm
  -- evmLt on high parts
  have hLt_hi : evmLt (eps3 / 2 ^ 86) (nat_rem / 2 ^ 86) =
      if eps3 / 2 ^ 86 < nat_rem / 2 ^ 86 then 1 else 0 :=
    evmLt_eq' _ _ heps3_hi_wm hrem_hi_wm
  -- evmEq on high parts
  have hEq_hi : evmEq (eps3 / 2 ^ 86) (nat_rem / 2 ^ 86) =
      if eps3 / 2 ^ 86 = nat_rem / 2 ^ 86 then 1 else 0 :=
    evmEq_eq' _ _ heps3_hi_wm hrem_hi_wm
  -- Low parts: evmAnd with mask86 = mod 2^86
  have hAnd_eps3 : evmAnd eps3 77371252455336267181195263 = eps3 % 2 ^ 86 :=
    evmAnd_mask86_eq_mod eps3 heps3_wm'
  have hAnd_rem : evmAnd nat_rem 77371252455336267181195263 = nat_rem % 2 ^ 86 :=
    evmAnd_mask86_eq_mod nat_rem hrem_wm
  -- Low part products
  have heps3_lo_wm : eps3 % 2 ^ 86 < WORD_MOD := by
    unfold WORD_MOD; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos 86)) (by omega)
  have hrem_lo_wm : nat_rem % 2 ^ 86 < WORD_MOD := by
    unfold WORD_MOD; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos 86)) (by omega)
  have hMul_lo : evmMul (eps3 % 2 ^ 86) m = ((eps3 % 2 ^ 86) * m) % WORD_MOD :=
    evmMul_eq' _ _ heps3_lo_wm hm_wm
  -- (eps3 % 2^86) * m < 2^86 * 2^85 = 2^171 < WORD_MOD
  have hprod_eps3_bound : (eps3 % 2 ^ 86) * m < 2 ^ 171 :=
    calc (eps3 % 2 ^ 86) * m
        < 2 ^ 86 * m := Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos 86)) (by omega)
      _ < 2 ^ 86 * 2 ^ 85 := Nat.mul_lt_mul_of_pos_left hm_hi (Nat.two_pow_pos 86)
      _ = 2 ^ 171 := by rw [← Nat.pow_add]
  have hprod_eps3_wm : (eps3 % 2 ^ 86) * m < WORD_MOD := by unfold WORD_MOD; omega
  rw [Nat.mod_eq_of_lt hprod_eps3_wm] at hMul_lo
  -- evmShl 86 (rem % 2^86) = (rem % 2^86) * 2^86
  have hShl_rem : evmShl (evmAnd (evmAnd 86 255) 255) (nat_rem % 2 ^ 86) =
      (nat_rem % 2 ^ 86) * 2 ^ 86 := by
    rw [qc_const_86, evmShl_eq' 86 (nat_rem % 2 ^ 86) (by omega) hrem_lo_wm]
    -- (rem % 2^86) * 2^86 < 2^86 * 2^86 = 2^172 < WORD_MOD
    have : (nat_rem % 2 ^ 86) * 2 ^ 86 < 2 ^ 172 :=
      calc (nat_rem % 2 ^ 86) * 2 ^ 86
          < 2 ^ 86 * 2 ^ 86 := Nat.mul_lt_mul_of_pos_right
            (Nat.mod_lt _ (Nat.two_pow_pos 86)) (Nat.two_pow_pos 86)
        _ = 2 ^ 172 := by rw [← Nat.pow_add]
    exact Nat.mod_eq_of_lt (by unfold WORD_MOD; omega)
  -- evmLt on low products
  have hprod_rem_bound : (nat_rem % 2 ^ 86) * 2 ^ 86 < WORD_MOD := by
    calc (nat_rem % 2 ^ 86) * 2 ^ 86
        < 2 ^ 86 * 2 ^ 86 := Nat.mul_lt_mul_of_pos_right
          (Nat.mod_lt _ (Nat.two_pow_pos 86)) (Nat.two_pow_pos 86)
      _ = 2 ^ 172 := by rw [← Nat.pow_add]
    unfold WORD_MOD; omega
  have hLt_lo : evmLt ((eps3 % 2 ^ 86) * m) ((nat_rem % 2 ^ 86) * 2 ^ 86) =
      if (eps3 % 2 ^ 86) * m < (nat_rem % 2 ^ 86) * 2 ^ 86 then 1 else 0 :=
    evmLt_eq' _ _ hprod_eps3_wm hprod_rem_bound
  -- ======== Simplify the check in hr1_eq using rw ========
  rw [hShr_eps3, hShr_rem, hLt_hi, hAnd_eps3, hAnd_rem, hMul_lo, hShl_rem, hLt_lo,
      hEq_hi] at hr1_eq
  -- Reduce evmAnd/evmOr on boolean results to &&&/|||
  rw [evmAnd_eq'
      (if eps3 / 2 ^ 86 = nat_rem / 2 ^ 86 then 1 else 0)
      (if (eps3 % 2 ^ 86) * m < (nat_rem % 2 ^ 86) * 2 ^ 86 then 1 else 0)
      (by split <;> unfold WORD_MOD <;> omega)
      (by split <;> unfold WORD_MOD <;> omega)] at hr1_eq
  rw [evmOr_eq'
      (if eps3 / 2 ^ 86 < nat_rem / 2 ^ 86 then 1 else 0)
      ((if eps3 / 2 ^ 86 = nat_rem / 2 ^ 86 then 1 else 0) &&&
       (if (eps3 % 2 ^ 86) * m < (nat_rem % 2 ^ 86) * 2 ^ 86 then 1 else 0))
      (by split <;> unfold WORD_MOD <;> omega)
      (by have := and_le_one _ _
            (by split <;> omega : (if eps3 / 2 ^ 86 = nat_rem / 2 ^ 86 then 1 else 0) ≤ 1)
            (by split <;> omega : (if (eps3 % 2 ^ 86) * m < (nat_rem % 2 ^ 86) * 2 ^ 86 then 1 else 0) ≤ 1)
          unfold WORD_MOD; omega)] at hr1_eq
  -- ======== evmAdd simplifications ========
  -- Abbreviate the check value
  generalize hcheck : (if eps3 / 2 ^ 86 < nat_rem / 2 ^ 86 then 1 else 0) |||
      ((if eps3 / 2 ^ 86 = nat_rem / 2 ^ 86 then 1 else 0) &&&
       (if (eps3 % 2 ^ 86) * m < (nat_rem % 2 ^ 86) * 2 ^ 86 then 1 else 0)) = check at hr1_eq
  have hcheck_le : check ≤ 1 := by
    rw [← hcheck]
    exact or_le_one _ _
      (by split <;> omega)
      (and_le_one _ _
        (by split <;> omega) (by split <;> omega))
  -- Simplify the two evmAdd calls
  have h_rloc_wm : nat_r_lo - c < WORD_MOD := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hr_lo_wm
  have h_check_wm : check < WORD_MOD := by unfold WORD_MOD; omega
  have h_inner : nat_r_lo - c + check < WORD_MOD := by unfold WORD_MOD; omega
  rw [evmAdd_eq' _ _ h_rloc_wm h_check_wm h_inner,
      evmAdd_eq' _ _ hR_wm h_inner (by unfold WORD_MOD; omega)] at hr1_eq
  -- Now hr1_eq : m * 2^86 + (nat_r_lo - c + check) = m * 2^86 + nat_r_lo - c + 1
  -- Extract check = 1
  have hcheck_eq_1 : check = 1 := by omega
  -- ======== Case split using or_and_eq_one_cases ========
  rw [← hcheck] at hcheck_eq_1
  have h_cases := or_and_eq_one_cases _ _ _
    (by split <;> omega) (by split <;> omega) (by split <;> omega)
    hcheck_eq_1
  rcases h_cases with h_hi_lt | ⟨h_hi_eq, h_lo_lt⟩
  · -- Case 1: eps3 / 2^86 < nat_rem / 2^86
    have : eps3 / 2 ^ 86 < nat_rem / 2 ^ 86 := by
      by_cases h : eps3 / 2 ^ 86 < nat_rem / 2 ^ 86
      · exact h
      · simp [h] at h_hi_lt
    have hlt := div_lt_implies_lt eps3 nat_rem this
    -- eps3 * R ≤ rem * 2^172 from eps3 < rem and R ≤ 2^172
    exact eps3_lt_rem_implies_prod_le eps3 nat_rem (m * 2 ^ 86)
      (by omega : m * 2 ^ 86 ≤ 2 ^ 172) hlt
  · -- Case 2: eps3 / 2^86 = nat_rem / 2^86 ∧ (eps3 % 2^86) * m < (nat_rem % 2^86) * 2^86
    have h_eq86 : eps3 / 2 ^ 86 = nat_rem / 2 ^ 86 := by
      by_cases h : eps3 / 2 ^ 86 = nat_rem / 2 ^ 86
      · exact h
      · simp [h] at h_hi_eq
    have h_lo86 : (eps3 % 2 ^ 86) * m < (nat_rem % 2 ^ 86) * 2 ^ 86 := by
      by_cases h : (eps3 % 2 ^ 86) * m < (nat_rem % 2 ^ 86) * 2 ^ 86
      · exact h
      · simp [h] at h_lo_lt
    -- eps3 * (m * 2^86) ≤ rem * 2^172 from the split-limb comparison
    exact split_limb_implies_prod_le eps3 nat_rem m
      (by omega : m ≤ 2 ^ 86) h_eq86 h_lo86

-- ============================================================================
-- r_qc³ < x_norm: the algebraic core
-- ============================================================================

/-- When the undershoot check fires (hr1_eq), r_qc³ < x_norm.
    Proof: decompose x_norm = R³ + 3R²·r_lo + rem·2^172 + c_tail,
    expand r_qc³ = (R+t)³ = R³ + 3R²t + 3Rt² + t³ where t = r_lo - c.
    x_norm - r_qc³ = 3R²c + rem·2^172 + c_tail - 3Rt² - t³.
    From undershoot: rem·2^172 ≥ 3Rε ⟹ 3R²c + rem·2^172 ≥ 3R·r_lo².
    From sq_sum_expand: 3R·r_lo² = 3Rt² + 6Rtc + 3Rc², so t³ < 6Rtc + 3Rc². -/
private theorem r_qc_cube_lt_x_norm (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD)
    (m : Nat) (hm_eq : m = icbrt (x_hi_1 / 4))
    (nat_r_lo nat_rem : Nat)
    (hr_lo_eq : nat_r_lo = ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) / (3 * (m * m)))
    (hrem_eq : nat_rem = ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) % (3 * (m * m)))
    (hr1_eq : model_cbrtQuadraticCorrection_evm m nat_r_lo nat_rem =
        m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86) + 1) :
    (m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86)) *
    (m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86)) *
    (m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86)) <
    x_hi_1 * 2 ^ 256 + x_lo_1 := by
  -- ======== Base case bounds ========
  have hbc := model_cbrtBaseCase_evm_correct x_hi_1 hxhi_lo hxhi_hi
  simp only at hbc
  rw [show icbrt (x_hi_1 / 4) = m from hm_eq.symm] at hbc
  have hm_lo : 2 ^ 83 ≤ m := hbc.2.2.2.1
  have hm_hi : m < 2 ^ 85 := hbc.2.2.2.2.1
  have hcube_le_w : m * m * m ≤ x_hi_1 / 4 := hbc.2.2.2.2.2.1
  have hm_wm : m < WORD_MOD := hbc.2.2.2.2.2.2.2.1
  have hm_pos : 2 ≤ m := Nat.le_trans (show 2 ≤ 2 ^ 83 from by
    rw [show (2 : Nat) ^ 83 = 2 * 2 ^ 82 from by
      rw [show (83 : Nat) = 1 + 82 from rfl, Nat.pow_add]]; omega) hm_lo
  have hR_pos : 0 < m * 2 ^ 86 := by omega
  have hd_pos : 0 < 3 * (m * m) :=
    Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
  have hres_bound : x_hi_1 / 4 - m * m * m ≤ 3 * (m * m) + 3 * m := hbc.2.2.2.2.2.2.1
  have hlimb_86 : (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86 := by
    have : x_hi_1 % 4 < 4 := Nat.mod_lt _ (by omega)
    have : x_lo_1 / 2 ^ 172 < 2 ^ 84 := by unfold WORD_MOD at hxlo; omega
    omega
  have hr_lo_bound : nat_r_lo < 2 ^ 87 := by
    rw [hr_lo_eq, Nat.div_lt_iff_lt_mul hd_pos]
    have h2m : 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
    calc ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
            (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172))
        < ((x_hi_1 / 4 - m * m * m) + 1) * 2 ^ 86 := by omega
      _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by apply Nat.mul_le_mul_right; omega
      _ ≤ (2 * (3 * (m * m))) * 2 ^ 86 := by apply Nat.mul_le_mul_right; omega
      _ = 2 ^ 87 * (3 * (m * m)) := by
          rw [show (2 : Nat) ^ 87 = 2 * 2 ^ 86 from by
            rw [show (87 : Nat) = 1 + 86 from rfl, Nat.pow_add]]; omega
  have hr_lo_wm : nat_r_lo < WORD_MOD := by unfold WORD_MOD; omega
  have hmm_hi : m * m < 2 ^ 170 :=
    calc m * m < m * 2 ^ 85 := Nat.mul_lt_mul_of_pos_left hm_hi (by omega)
      _ ≤ 2 ^ 85 * 2 ^ 85 := Nat.mul_le_mul_right _ (Nat.le_of_lt hm_hi)
      _ = 2 ^ 170 := by rw [← Nat.pow_add]
  have hd_wm : 3 * (m * m) < WORD_MOD := by unfold WORD_MOD; omega
  have hrem_wm : nat_rem < WORD_MOD := by
    rw [hrem_eq]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hd_pos) (Nat.le_of_lt hd_wm)
  have hc_gt1 : nat_r_lo * nat_r_lo / (m * 2 ^ 86) > 1 := by
    by_cases hcgt : nat_r_lo * nat_r_lo / (m * 2 ^ 86) > 1
    · exact hcgt
    · exfalso
      have hexact := model_cbrtQuadraticCorrection_evm_exact_when_c_le1
          m nat_r_lo nat_rem hm_wm hr_lo_wm hrem_wm hm_pos hm_hi hr_lo_bound (by omega)
      omega
  -- ======== Abbreviate ========
  let R := m * 2 ^ 86
  let c := nat_r_lo * nat_r_lo / R
  let ε := nat_r_lo * nat_r_lo % R
  let t := nat_r_lo - c
  -- ======== c ≤ nat_r_lo ========
  have hc_le : c ≤ nat_r_lo := by
    show nat_r_lo * nat_r_lo / (m * 2 ^ 86) ≤ nat_r_lo
    have hR_gt : nat_r_lo < m * 2 ^ 86 := by omega
    cases Nat.eq_or_lt_of_le (Nat.zero_le nat_r_lo) with
    | inl h => rw [← h]; simp
    | inr h =>
      exact Nat.le_of_lt ((Nat.div_lt_iff_lt_mul hR_pos).mpr
        (Nat.mul_lt_mul_of_pos_left hR_gt h))
  -- ======== Undershoot: ε * 3 * R ≤ nat_rem * 2^172 ========
  have hundershoot := undershoot_implies_rem_gt_3Reps m nat_r_lo nat_rem
      hm_wm hr_lo_wm hrem_wm hm_pos hm_hi hr_lo_bound hc_gt1 hr1_eq
  -- ======== x_norm decomposition ========
  have hx_decomp := x_norm_decomp x_hi_1 x_lo_1 (m * m * m) hcube_le_w
  have hn_full := Nat.div_add_mod
      ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) (3 * (m * m))
  have h_num_eq : (x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
      (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172) =
      3 * (m * m) * nat_r_lo + nat_rem := by
    rw [hr_lo_eq, hrem_eq]; exact hn_full.symm
  have hR3 := R_cube_factor m
  have hd_eq_3R2 := d_pow172_eq_3R_sq m
  -- x_norm lower bound: x_norm ≥ R³ + 3R²·r_lo (same as sub-lemma B)
  have hx_lb : m * m * m * 2 ^ 258 + 3 * (m * m) * nat_r_lo * 2 ^ 172 ≤
      x_hi_1 * 2 ^ 256 + x_lo_1 := by
    rw [hx_decomp, h_num_eq, Nat.add_mul, Nat.mul_assoc]; omega
  have hx_lb2 : R * R * R + 3 * (R * R) * nat_r_lo ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := by
    calc R * R * R + 3 * (R * R) * nat_r_lo
        = m * m * m * 2 ^ 258 + 3 * (m * m) * nat_r_lo * 2 ^ 172 := by
          rw [← hR3]
          show R * R * R + 3 * (R * R) * nat_r_lo =
            R * R * R + 3 * (m * m) * nat_r_lo * 2 ^ 172
          rw [← hd_eq_3R2]
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := hx_lb
  -- ======== Division/mod identity ========
  have hdm := Nat.div_add_mod (nat_r_lo * nat_r_lo) R
  -- ======== Floor division bound: r_lo² < (c+1)R ========
  have hcR_lt : nat_r_lo * nat_r_lo < (c + 1) * R := by
    show nat_r_lo * nat_r_lo < (nat_r_lo * nat_r_lo / R + 1) * R
    have hmod_lt := Nat.mod_lt (nat_r_lo * nat_r_lo) hR_pos
    calc nat_r_lo * nat_r_lo
        = R * (nat_r_lo * nat_r_lo / R) + nat_r_lo * nat_r_lo % R := hdm.symm
      _ < R * (nat_r_lo * nat_r_lo / R) + R := Nat.add_lt_add_left hmod_lt _
      _ = R * (nat_r_lo * nat_r_lo / R + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = (nat_r_lo * nat_r_lo / R + 1) * R := Nat.mul_comm _ _
  -- t ≤ r_lo, t² ≤ r_lo² < (c+1)R
  have ht_le : t ≤ nat_r_lo := Nat.sub_le _ _
  have ht_sq_lt : t * t < (c + 1) * R :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul ht_le ht_le) hcR_lt
  -- ======== t³ < 6Rtc + 3Rc² ========
  have h_t_cube_lt : t * t * t < 6 * R * t * c + 3 * R * (c * c) := by
    cases Nat.eq_or_lt_of_le (Nat.zero_le t) with
    | inl ht0 =>
      rw [← ht0]; simp
      have hc_pos : 0 < c := Nat.lt_trans (by omega : 0 < 1) hc_gt1
      exact Nat.mul_pos (Nat.mul_pos (by omega : 0 < 3) hR_pos)
        (Nat.mul_pos hc_pos hc_pos)
    | inr ht_pos =>
      have h1 : t * (t * t) < t * ((c + 1) * R) :=
        Nat.mul_lt_mul_of_pos_left ht_sq_lt ht_pos
      rw [show t * t * t = t * (t * t) from Nat.mul_assoc _ _ _]
      calc t * (t * t)
          < t * ((c + 1) * R) := h1
        _ ≤ t * (6 * c * R) := by
            apply Nat.mul_le_mul_left
            -- (c + 1) * R ≤ (6 * c) * R
            exact Nat.mul_le_mul_right R (show c + 1 ≤ 6 * c from by
              have : c > 1 := hc_gt1; omega)
        _ = 6 * R * t * c := by
            suffices h : (↑(t * (6 * c * R)) : Int) = ↑(6 * R * t * c) by exact_mod_cast h
            push_cast; simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
        _ ≤ 6 * R * t * c + 3 * R * (c * c) := Nat.le_add_right _ _
  -- ======== 3Rt² + 6Rtc + 3Rc² = 3R·r_lo² (from sq_sum_expand) ========
  have htc_rlo : t + c = nat_r_lo := by show nat_r_lo - c + c = nat_r_lo; omega
  have hrlo_sq := sq_sum_expand t c
  have h3R_expand : 3 * R * (t * t) + (6 * R * t * c + 3 * R * (c * c)) =
      3 * R * (nat_r_lo * nat_r_lo) := by
    rw [← htc_rlo, hrlo_sq]
    suffices h : (↑(3 * R * (t * t) + (6 * R * t * c + 3 * R * (c * c))) : Int) =
        ↑(3 * R * (t * t + 2 * t * c + c * c)) by
      have h2 : (↑(3 * R * (t * t + 2 * t * c + c * c)) : Int) =
          ↑(3 * R * (t * t) + (6 * R * t * c + 3 * R * (c * c))) := h.symm
      exact_mod_cast h2.symm
    push_cast
    simp [Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  -- ======== 3R²c + rem·2^172 ≥ 3R·r_lo² (from undershoot + div_add_mod) ========
  have h3R_rlo2 : 3 * (R * R) * c + ε * 3 * R = 3 * R * (nat_r_lo * nat_r_lo) := by
    -- 3R²c + 3Rε = 3R(Rc + ε) = 3R·r_lo²
    have h_factor : 3 * (R * R) * c + ε * 3 * R = 3 * R * (R * c + ε) := by
      suffices h : (↑(3 * (R * R) * c + ε * 3 * R) : Int) = ↑(3 * R * (R * c + ε)) by
        exact_mod_cast h
      push_cast
      simp only [Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [h_factor, show R * c + ε = nat_r_lo * nat_r_lo from hdm]
  have h_dom : 3 * R * (nat_r_lo * nat_r_lo) ≤
      3 * (R * R) * c + nat_rem * 2 ^ 172 := by
    calc 3 * R * (nat_r_lo * nat_r_lo)
        = 3 * (R * R) * c + ε * 3 * R := h3R_rlo2.symm
      _ ≤ 3 * (R * R) * c + nat_rem * 2 ^ 172 := Nat.add_le_add_left hundershoot _
  -- ======== Final chain: (R+t)³ < x_norm ========
  -- Goal: (m*2^86 + nat_r_lo - c)³ < x_norm.
  -- Since R, c, t are let-bound, goal is (R + nat_r_lo - c)³ < x_norm,
  -- which is definitionally (R + t + c - c)... we use Nat.add_sub_cancel:
  -- R + nat_r_lo - c = R + (nat_r_lo - c) = R + t (via hc_le and omega)
  -- Suffices: (R + t)³ < x_norm
  -- (R + t)³ = R³ + 3R²t + 3Rt² + t³  [cube_sum_expand]
  -- From algebraic chain + undershoot:
  --   3Rt² + t³ < 3R·r_lo² ≤ 3R²c + rem·2^172 ≤ 3R²r_lo  (NOT what I need)
  -- Actually: 3Rt² + t³ < 3R·r_lo² ≤ 3R²c + rem·2^172 (from h_dom)
  -- So: (R + t)³ = R³ + 3R²t + 3Rt² + t³ < R³ + 3R²t + 3R²c + rem·2^172
  --             = R³ + 3R²(t + c) + rem·2^172 = R³ + 3R²·r_lo + rem·2^172
  --             ≤ x_norm (from hx_lb2, which drops rem·2^172 and c_tail)
  -- WAIT: hx_lb2 only gives R³ + 3R²·r_lo ≤ x_norm. I need a bound with rem·2^172.
  -- BUT: 3Rt² + t³ < 3R²c + rem·2^172, and I also need ≤ 3R²·r_lo.
  --   3R²c ≤ 3R²·r_lo (since c ≤ r_lo). So 3Rt² + t³ < 3R²·r_lo + rem·2^172.
  --   Then: (R+t)³ < R³ + 3R²t + 3R²·r_lo + rem·2^172 ≤ R³ + 3R²·(t + r_lo) + rem...
  --   Hmm, this gives 3R²(t + r_lo), not 3R²·r_lo. Let me reconsider.
  --
  -- Correct chain: (R+t)³ = R³ + 3R²t + 3Rt² + t³
  -- Need to show < x_norm.
  -- x_norm ≥ R³ + 3R²·r_lo (from hx_lb2).
  -- Suffices: 3R²t + 3Rt² + t³ < 3R²·r_lo, i.e., 3Rt² + t³ < 3R²(r_lo - t) = 3R²c.
  -- But 3Rt² + t³ < 3R²c is NOT always true (as analyzed).
  -- The correct approach: use x_norm ≥ R³ + 3R²·r_lo + rem·2^172 (with rem term).
  -- But hx_lb2 drops the rem term.
  -- Need a TIGHTER lower bound: hx_lb (line above) gives m³·2^258 + 3m²·r_lo·2^172 ≤ x_norm.
  -- Which is R³ + 3R²·r_lo ≤ x_norm. No rem term.
  -- For the full bound, need: x_norm = R³ + 3R²r_lo + rem·2^172 + c_tail.
  -- But proving this exact equality through R-based terms was the problem.
  --
  -- Alternative: prove the FULL lower bound including rem*2^172:
  -- x_norm ≥ R³ + 3R²r_lo + rem*2^172
  -- From hx_decomp + h_num_eq: x_norm = m³·2^258 + (3m²·r_lo + rem)·2^172 + c_tail
  --   ≥ m³·2^258 + (3m²·r_lo + rem)·2^172
  --   = m³·2^258 + 3m²·r_lo·2^172 + rem·2^172
  --   = R³ + 3R²·r_lo + rem·2^172 (converting via hR3, hd_eq_3R2)
  have hx_lb3 : R * R * R + 3 * (R * R) * nat_r_lo + nat_rem * 2 ^ 172 ≤
      x_hi_1 * 2 ^ 256 + x_lo_1 := by
    have hx_lb_m : m * m * m * 2 ^ 258 + 3 * (m * m) * nat_r_lo * 2 ^ 172 +
        nat_rem * 2 ^ 172 ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := by
      rw [hx_decomp, h_num_eq, Nat.add_mul, Nat.mul_assoc]; omega
    have h3R2rlo : 3 * (R * R) * nat_r_lo = 3 * (m * m) * nat_r_lo * 2 ^ 172 := by
      show 3 * (m * 2 ^ 86 * (m * 2 ^ 86)) * nat_r_lo =
        3 * (m * m) * nat_r_lo * 2 ^ 172
      rw [← hd_eq_3R2]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    calc R * R * R + 3 * (R * R) * nat_r_lo + nat_rem * 2 ^ 172
        = m * m * m * 2 ^ 258 + 3 * (m * m) * nat_r_lo * 2 ^ 172 +
            nat_rem * 2 ^ 172 := by rw [hR3, h3R2rlo]
      _ ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := hx_lb_m
  -- Now the final chain works:
  -- (R + t)³ = R³ + 3R²t + 3Rt² + t³
  -- 3Rt² + t³ < 3R·r_lo² ≤ 3R²c + rem·2^172
  -- So (R+t)³ < R³ + 3R²t + 3R²c + rem·2^172 = R³ + 3R²·r_lo + rem·2^172 ≤ x_norm
  -- Use: R + nat_r_lo - c = R + t (definitionally, omega handles Nat sub)
  show (R + nat_r_lo - c) * (R + nat_r_lo - c) * (R + nat_r_lo - c) <
      x_hi_1 * 2 ^ 256 + x_lo_1
  have hrqc_eq : R + nat_r_lo - c = R + t := by omega
  rw [hrqc_eq, cube_sum_expand R t]
  calc R * R * R + 3 * (R * R) * t + 3 * R * (t * t) + t * t * t
      = R * R * R + 3 * (R * R) * t + (3 * R * (t * t) + t * t * t) := by omega
    _ < R * R * R + 3 * (R * R) * t + (3 * (R * R) * c + nat_rem * 2 ^ 172) := by
        -- Need: 3Rt² + t³ < 3R²c + rem·2^172
        -- Chain: 3Rt² + t³ < 3R·r_lo² ≤ 3R²c + rem·2^172
        have : 3 * R * (t * t) + t * t * t < 3 * R * (nat_r_lo * nat_r_lo) := by
          calc 3 * R * (t * t) + t * t * t
              < 3 * R * (t * t) + (6 * R * t * c + 3 * R * (c * c)) := by omega
            _ = 3 * R * (nat_r_lo * nat_r_lo) := h3R_expand
        omega
    _ = R * R * R + (3 * (R * R) * t + 3 * (R * R) * c) + nat_rem * 2 ^ 172 := by omega
    _ = R * R * R + 3 * (R * R) * (t + c) + nat_rem * 2 ^ 172 := by rw [← Nat.mul_add]
    _ = R * R * R + 3 * (R * R) * nat_r_lo + nat_rem * 2 ^ 172 := by rw [htc_rlo]
    _ ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := hx_lb3

-- ============================================================================
-- ============================================================================
-- Undershoot algebraic core: r_qc³ < x_norm when undershoot fires
-- ============================================================================

/-- When the QC model returns r_qc + 1 (undershoot correction applied),
    then r_qc³ < x_norm and (r_qc+1)³ < WORD_MOD². -/
theorem qc_undershoot_cube_lt (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD)
    (m : Nat) (hm_eq : m = icbrt (x_hi_1 / 4))
    (nat_r_lo nat_rem : Nat)
    (hr_lo_eq : nat_r_lo = ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) / (3 * (m * m)))
    (hrem_eq : nat_rem = ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) % (3 * (m * m)))
    (hr1_eq : model_cbrtQuadraticCorrection_evm m nat_r_lo nat_rem =
        m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86) + 1) :
    let r_qc := m * 2 ^ 86 + nat_r_lo - nat_r_lo * nat_r_lo / (m * 2 ^ 86)
    r_qc * r_qc * r_qc < x_hi_1 * 2 ^ 256 + x_lo_1 ∧
    (r_qc + 1) * (r_qc + 1) * (r_qc + 1) < WORD_MOD * WORD_MOD := by
  simp only
  -- ======== Base case bounds ========
  have hbc := model_cbrtBaseCase_evm_correct x_hi_1 hxhi_lo hxhi_hi
  simp only at hbc
  rw [show icbrt (x_hi_1 / 4) = m from hm_eq.symm] at hbc
  have hm_lo : 2 ^ 83 ≤ m := hbc.2.2.2.1
  have hm_hi : m < 2 ^ 85 := hbc.2.2.2.2.1
  have hcube_le_w : m * m * m ≤ x_hi_1 / 4 := hbc.2.2.2.2.2.1
  have hm_wm : m < WORD_MOD := hbc.2.2.2.2.2.2.2.1
  have hm_pos : 2 ≤ m := Nat.le_trans (show 2 ≤ 2 ^ 83 from by
    rw [show (2 : Nat) ^ 83 = 2 * 2 ^ 82 from by
      rw [show (83 : Nat) = 1 + 82 from rfl, Nat.pow_add]]; omega) hm_lo
  have hR_pos : 0 < m * 2 ^ 86 := by omega
  have hd_pos : 0 < 3 * (m * m) :=
    Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
  -- ======== r_lo and rem bounds ========
  have hres_bound : x_hi_1 / 4 - m * m * m ≤ 3 * (m * m) + 3 * m := hbc.2.2.2.2.2.2.1
  have h2m : 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
  have hlimb_86 : (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86 := by
    have : x_hi_1 % 4 < 4 := Nat.mod_lt _ (by omega)
    have : x_lo_1 / 2 ^ 172 < 2 ^ 84 := by unfold WORD_MOD at hxlo; omega
    omega
  have hr_lo_bound : nat_r_lo < 2 ^ 87 := by
    rw [hr_lo_eq, Nat.div_lt_iff_lt_mul hd_pos]
    calc ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
            (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172))
        < ((x_hi_1 / 4 - m * m * m) + 1) * 2 ^ 86 := by omega
      _ ≤ (3 * (m * m) + 3 * m + 1) * 2 ^ 86 := by apply Nat.mul_le_mul_right; omega
      _ ≤ (2 * (3 * (m * m))) * 2 ^ 86 := by apply Nat.mul_le_mul_right; omega
      _ = 2 ^ 87 * (3 * (m * m)) := by
          rw [show (2 : Nat) ^ 87 = 2 * 2 ^ 86 from by
            rw [show (87 : Nat) = 1 + 86 from rfl, Nat.pow_add]]; omega
  have hr_lo_wm : nat_r_lo < WORD_MOD := by unfold WORD_MOD; omega
  have hmm_hi : m * m < 2 ^ 170 :=
    calc m * m < m * 2 ^ 85 := Nat.mul_lt_mul_of_pos_left hm_hi (by omega)
      _ ≤ 2 ^ 85 * 2 ^ 85 := Nat.mul_le_mul_right _ (Nat.le_of_lt hm_hi)
      _ = 2 ^ 170 := by rw [← Nat.pow_add]
  have hd_wm : 3 * (m * m) < WORD_MOD := by unfold WORD_MOD; omega
  have hrem_wm : nat_rem < WORD_MOD := by
    rw [hrem_eq]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hd_pos) (Nat.le_of_lt hd_wm)
  -- ======== Extract c > 1 ========
  have hc_gt1 : nat_r_lo * nat_r_lo / (m * 2 ^ 86) > 1 := by
    by_cases hcgt : nat_r_lo * nat_r_lo / (m * 2 ^ 86) > 1
    · exact hcgt
    · exfalso
      have hexact := model_cbrtQuadraticCorrection_evm_exact_when_c_le1
          m nat_r_lo nat_rem hm_wm hr_lo_wm hrem_wm hm_pos hm_hi hr_lo_bound (by omega)
      omega
  -- ======== r_qc ≤ R_MAX ========
  have hE1 := r_qc_le_r_max x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  simp only at hE1
  rw [show icbrt (x_hi_1 / 4) = m from hm_eq.symm,
      show ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
        (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) / (3 * (m * m)) = nat_r_lo
      from hr_lo_eq.symm] at hE1
  constructor
  · -- Conjunct 1: r_qc³ < x_norm
    -- Delegated to r_qc_cube_lt_x_norm helper lemma
    exact r_qc_cube_lt_x_norm x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
        m hm_eq nat_r_lo nat_rem hr_lo_eq hrem_eq hr1_eq
  · -- Conjunct 2: (r_qc+1)³ < WORD_MOD²
    -- From r_plus_rlo_le_rmax_succ: R + r_lo ≤ R_MAX + 1.
    -- From c ≥ 2: r_qc + 1 = R + r_lo - c + 1 ≤ R_MAX + 1 - 2 + 1 = R_MAX.
    -- Then (r_qc+1)³ ≤ R_MAX³ < WORD_MOD².
    have hRrlo := r_plus_rlo_le_rmax_succ x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
    simp only at hRrlo
    rw [show icbrt (x_hi_1 / 4) = m from hm_eq.symm,
        show ((x_hi_1 / 4 - m * m * m) * 2 ^ 86 +
          (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) / (3 * (m * m)) = nat_r_lo
        from hr_lo_eq.symm] at hRrlo
    -- hRrlo : m * 2^86 + nat_r_lo ≤ R_MAX + 1
    -- hc_gt1 : c > 1, i.e., c ≥ 2
    -- Goal: (R + r_lo - c + 1)³ < WORD_MOD²
    -- First show r_qc + 1 ≤ R_MAX via omega (c ≥ 2 and R + r_lo ≤ R_MAX + 1)
    have hrqc_succ_le : m * 2 ^ 86 + nat_r_lo -
        nat_r_lo * nat_r_lo / (m * 2 ^ 86) + 1 ≤ R_MAX := by omega
    exact Nat.lt_of_le_of_lt (cube_monotone hrqc_succ_le) r_max_cube_lt_wm2

-- ============================================================================
-- Full composition within 1 ulp
-- ============================================================================

/-- After base case + Karatsuba + quadratic correction, the result is within 1 of
    icbrt(x_norm) where x_norm = x_hi_1 * 2^256 + x_lo_1. -/
theorem composition_within_1ulp (x_hi_1 x_lo_1 : Nat)
    (hxhi_lo : 2 ^ 253 ≤ x_hi_1) (hxhi_hi : x_hi_1 < WORD_MOD)
    (hxlo : x_lo_1 < WORD_MOD) :
    let x_norm := x_hi_1 * 2 ^ 256 + x_lo_1
    let w := x_hi_1 / 4
    let m := icbrt w  -- r_hi after base case
    let res := w - m * m * m
    let d := 3 * (m * m)
    let limb_hi := (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
    let r_lo := (res * 2 ^ 86 + limb_hi) / d
    let R := m * 2 ^ 86
    let correction := r_lo * r_lo / R
    let r_qc := R + r_lo - correction
    icbrt x_norm ≤ r_qc + 1 ∧ r_qc ≤ icbrt x_norm + 1 ∧
    r_qc < WORD_MOD ∧
    r_qc * r_qc * r_qc < WORD_MOD * WORD_MOD ∧
    r_qc + 1 < WORD_MOD ∧
    (r_qc * r_qc * r_qc > x_norm →
      icbrt x_norm * icbrt x_norm * icbrt x_norm < x_norm) := by
  -- Core properties from r_qc_properties (within 1 ulp + cube bound + overshoot)
  have h_props := r_qc_properties x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  -- Range bound from r_qc_lt_pow172 (r_qc < 2^172)
  have h_bound := r_qc_lt_pow172 x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  -- Unfold let-bindings so omega can see through them
  simp only at h_props h_bound ⊢
  refine ⟨h_props.1, h_props.2.1, ?_, h_props.2.2.1, ?_, h_props.2.2.2⟩
  · -- [3] r_qc < WORD_MOD: from h_bound (r_qc < 2^172 < WORD_MOD)
    unfold WORD_MOD; omega
  · -- [5] r_qc + 1 < WORD_MOD: from h_bound
    unfold WORD_MOD; omega

end Cbrt512Spec
