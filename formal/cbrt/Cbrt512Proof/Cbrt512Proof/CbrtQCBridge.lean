/-
  Quadratic correction EVM bridge: model_cbrtQuadraticCorrection_evm
  returns R + r_lo - c + undershoot where undershoot ∈ {0, 1}.
-/
import Cbrt512Proof.GeneratedCbrt512Model
import Cbrt512Proof.EvmBridge

namespace Cbrt512Spec

open Cbrt512GeneratedModel

-- ============================================================================
-- QC helper lemmas
-- ============================================================================

/-- The constant expression evmAnd(evmAnd(86,255),255) evaluates to 86. -/
theorem qc_const_86 : evmAnd (evmAnd 86 255) 255 = 86 := by
  unfold evmAnd u256 WORD_MOD; native_decide

/-- Bitwise OR of two values ≤ 1 is ≤ 1. -/
theorem or_le_one (a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) : a ||| b ≤ 1 := by
  have : a = 0 ∨ a = 1 := by omega
  have : b = 0 ∨ b = 1 := by omega
  rcases ‹a = 0 ∨ a = 1› with rfl | rfl <;> rcases ‹b = 0 ∨ b = 1› with rfl | rfl <;> decide

/-- evmLt returns a value ≤ 1. -/
theorem evmLt_le_one (a b : Nat) : evmLt a b ≤ 1 := by
  unfold evmLt; split <;> omega

/-- evmEq returns a value ≤ 1. -/
theorem evmEq_le_one (a b : Nat) : evmEq a b ≤ 1 := by
  unfold evmEq; split <;> omega

/-- Bitwise AND of two values ≤ 1 is ≤ 1. -/
theorem and_le_one (a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) : a &&& b ≤ 1 := by
  have : a = 0 ∨ a = 1 := by omega
  have : b = 0 ∨ b = 1 := by omega
  rcases ‹a = 0 ∨ a = 1› with rfl | rfl <;> rcases ‹b = 0 ∨ b = 1› with rfl | rfl <;> decide

/-- evmAnd of values ≤ 1 is ≤ 1. -/
theorem evmAnd_le_one (a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) :
    evmAnd a b ≤ 1 := by
  unfold evmAnd u256 WORD_MOD
  have ha' : a % 2 ^ 256 = a := Nat.mod_eq_of_lt (by omega)
  have hb' : b % 2 ^ 256 = b := Nat.mod_eq_of_lt (by omega)
  simp only [ha', hb']
  exact and_le_one a b ha hb

/-- evmOr of values ≤ 1 is ≤ 1. -/
theorem evmOr_le_one (a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) :
    evmOr a b ≤ 1 := by
  unfold evmOr u256 WORD_MOD
  have ha' : a % 2 ^ 256 = a := Nat.mod_eq_of_lt (by omega)
  have hb' : b % 2 ^ 256 = b := Nat.mod_eq_of_lt (by omega)
  simp only [ha', hb']
  exact or_le_one a b ha hb

/-- The undershoot check in the QC produces a value ≤ 1. -/
theorem qc_undershoot_le_one (eps3 rem r_hi : Nat) :
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


end Cbrt512Spec
