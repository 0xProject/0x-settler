/-
  Quadratic correction EVM bridge: model_cbrtQuadraticCorrection_evm
  returns R + r_lo - c + undershoot where undershoot ∈ {0, 1}.
-/
import Cbrt512Proof.GeneratedCbrt512Model
import Cbrt512Proof.CbrtNumericCerts
import Cbrt512Proof.EvmBridge

namespace Cbrt512Spec

open Cbrt512GeneratedModel

-- ============================================================================
-- QC helper lemmas
-- ============================================================================

private theorem pow86_lit :
    (77371252455336267181195264 : Nat) = 2 ^ 86 := by
  native_decide

/-- Bitwise OR of two values ≤ 1 is ≤ 1. -/
theorem or_le_one (a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) : a ||| b ≤ 1 := by
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
theorem and_le_one (a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) : a &&& b ≤ 1 := by
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

/-- Masking by `2^86 - 1` extracts the low 86 bits. -/
theorem evmAnd_mask86_eq_mod (x : Nat) (hx : x < WORD_MOD) :
    evmAnd x 77371252455336267181195263 = x % 2 ^ 86 := by
  have hmask_wm : (77371252455336267181195263 : Nat) < WORD_MOD := by
    unfold WORD_MOD
    omega
  rw [evmAnd_eq' x _ hx hmask_wm, mask_86_eq]
  exact Nat.and_two_pow_sub_one_eq_mod x 86

/-- If the QC check bit is zero, then either the high limb of `rem` is smaller,
    or the high limbs tie and the low-limb comparison fails. -/
private theorem qc_check_zero_cases (eps3 rem r_hi : Nat)
    (hcheck0 :
      ((if eps3 / 2 ^ 86 < rem / 2 ^ 86 then 1 else 0) |||
        ((if eps3 / 2 ^ 86 = rem / 2 ^ 86 then 1 else 0) &&&
         (if (eps3 % 2 ^ 86) * r_hi < (rem % 2 ^ 86) * 2 ^ 86 then 1 else 0))) = 0) :
    rem / 2 ^ 86 < eps3 / 2 ^ 86 ∨
      (rem / 2 ^ 86 = eps3 / 2 ^ 86 ∧
        (rem % 2 ^ 86) * 2 ^ 86 ≤ (eps3 % 2 ^ 86) * r_hi) := by
  by_cases h_hi_lt : rem / 2 ^ 86 < eps3 / 2 ^ 86
  · exact Or.inl h_hi_lt
  · have h_not_eps_lt_rem : ¬ eps3 / 2 ^ 86 < rem / 2 ^ 86 := by
      intro h
      have hge :
          1 ≤
            ((if eps3 / 2 ^ 86 < rem / 2 ^ 86 then 1 else 0) |||
              ((if eps3 / 2 ^ 86 = rem / 2 ^ 86 then 1 else 0) &&&
                (if (eps3 % 2 ^ 86) * r_hi < (rem % 2 ^ 86) * 2 ^ 86 then 1 else 0))) := by
        simp [h]
        exact Nat.left_le_or
      omega
    have h_hi_eq : rem / 2 ^ 86 = eps3 / 2 ^ 86 := by
      omega
    have h_lo_le : (rem % 2 ^ 86) * 2 ^ 86 ≤ (eps3 % 2 ^ 86) * r_hi := by
      by_cases h_lo_lt : (eps3 % 2 ^ 86) * r_hi < (rem % 2 ^ 86) * 2 ^ 86
      · simp [h_hi_eq, h_lo_lt] at hcheck0
      · exact Nat.not_lt.mp h_lo_lt
    exact Or.inr ⟨h_hi_eq, h_lo_le⟩

/-- If `a / 2^86 < b / 2^86`, then `a < b`. -/
theorem div_lt_implies_lt (a b : Nat)
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

/-- A split-limb comparison with equal high limbs implies the full-number bound. -/
private theorem split_limb_le_implies_le (a b m : Nat)
    (hm_le : m ≤ 2 ^ 86)
    (h_eq : a / 2 ^ 86 = b / 2 ^ 86)
    (h_lo : (a % 2 ^ 86) * 2 ^ 86 ≤ (b % 2 ^ 86) * m) :
    a ≤ b := by
  have h_lo86 : (a % 2 ^ 86) * 2 ^ 86 ≤ (b % 2 ^ 86) * 2 ^ 86 := by
    exact Nat.le_trans h_lo (Nat.mul_le_mul_left _ hm_le)
  have h_lo' : a % 2 ^ 86 ≤ b % 2 ^ 86 :=
    Nat.le_of_mul_le_mul_right h_lo86 (Nat.two_pow_pos 86)
  have hda := Nat.div_add_mod a (2 ^ 86)
  have hdb := Nat.div_add_mod b (2 ^ 86)
  rw [← hda, ← hdb, h_eq]
  omega

-- ============================================================================
-- Quadratic correction EVM bridge
-- ============================================================================

/-- Shared bounds and EVM reductions for all three QC bridge theorems. -/
private theorem qc_evm_setup (r_hi r_lo : Nat)
    (hr_hi : r_hi < WORD_MOD) (hr_lo : r_lo < WORD_MOD)
    (hr_hi_pos : 2 ≤ r_hi)
    (hr_hi_bound : r_hi < 2 ^ 85)
    (hr_lo_bound : r_lo < 2 ^ 87) :
    let R := r_hi * 2 ^ 86
    let c := r_lo * r_lo / R
    -- Bounds
    2 ^ 87 ≤ R ∧ R < 2 ^ 171 ∧ R < WORD_MOD ∧ 0 < R ∧
    r_lo * r_lo < WORD_MOD ∧ c ≤ r_lo ∧ c * R ≤ r_lo * r_lo ∧
    c < WORD_MOD ∧ c * R < WORD_MOD ∧
    -- EVM reductions
    evmShl (evmAnd (evmAnd 86 255) 255) r_hi = R ∧
    evmMul r_lo r_lo = r_lo * r_lo ∧
    evmDiv (r_lo * r_lo) R = c ∧
    evmMul c R = c * R ∧
    evmSub (r_lo * r_lo) (c * R) = r_lo * r_lo % R ∧
    r_lo * r_lo % R < WORD_MOD ∧
    (r_lo * r_lo % R) * 3 < WORD_MOD ∧
    evmMul (r_lo * r_lo % R) 3 = (r_lo * r_lo % R) * 3 ∧
    evmSub r_lo c = r_lo - c ∧
    evmGt c 1 = if c > 1 then 1 else 0 := by
  simp only
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
  have hcR_le : (r_lo * r_lo / (r_hi * 2 ^ 86)) * (r_hi * 2 ^ 86) ≤ r_lo * r_lo :=
    Nat.div_mul_le_self _ _
  let c := r_lo * r_lo / (r_hi * 2 ^ 86)
  have hc_wm : c < WORD_MOD := Nat.lt_of_le_of_lt hc_le hr_lo
  have hcR_wm : c * (r_hi * 2 ^ 86) < WORD_MOD :=
    Nat.lt_of_le_of_lt hcR_le hr_lo_sq_wm
  -- EVM reductions
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
  exact ⟨hR_ge, hR_lt, hR_wm, hR_pos, hr_lo_sq_wm, hc_le, hcR_le,
         hc_wm, hcR_wm, hR_eq, hSq_eq, hC_eq, hCR_eq, hResid_eq,
         hmod_lt, heps3_wm, hEps3_eq, hSub_eq, hGt_eq⟩

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
  obtain ⟨hR_ge, hR_lt, hR_wm, hR_pos, hr_lo_sq_wm, hc_le, hcR_le,
          hc_wm, hcR_wm, hR_eq, hSq_eq, hC_eq, hCR_eq, hResid_eq,
          hmod_lt, heps3_wm, hEps3_eq, hSub_eq, hGt_eq⟩ :=
    qc_evm_setup r_hi r_lo hr_hi hr_lo hr_hi_pos hr_hi_bound hr_lo_bound
  let c := r_lo * r_lo / (r_hi * 2 ^ 86)
  have hR_eq_lit : evmShl 86 r_hi = r_hi * 2 ^ 86 := by
    rw [evmShl_eq' 86 r_hi (by omega) hr_hi]
    exact Nat.mod_eq_of_lt hR_wm
  -- Unfold model and simplify
  unfold model_cbrtQuadraticCorrection_evm
  simp only [u256_id' r_hi hr_hi, u256_id' r_lo hr_lo, u256_id' rem hrem,
             hR_eq_lit, hSq_eq, hC_eq, hCR_eq, hResid_eq, hEps3_eq, hSub_eq, hGt_eq]
  -- Case split on c > 1
  by_cases hcgt : c > 1
  · -- Case c > 1: undershoot fires, result = R + (r_lo - c) + u where u ≤ 1
    have hcgt_lit : 1 < r_lo * r_lo / (r_hi * 77371252455336267181195264) := by
      simpa [c, pow86_lit] using hcgt
    have hsub_lit :
        r_lo - r_lo * r_lo / (r_hi * 77371252455336267181195264) = r_lo - c := by
      simp [c, pow86_lit]
    simp [pow86_lit, hcgt_lit]
    let us : Nat :=
      evmOr
        (evmLt (evmShr 86 (r_lo * r_lo % (r_hi * 77371252455336267181195264) * 3)) (evmShr 86 rem))
        (evmAnd
          (evmEq (evmShr 86 (r_lo * r_lo % (r_hi * 77371252455336267181195264) * 3)) (evmShr 86 rem))
          (evmLt
            (evmMul (evmAnd (r_lo * r_lo % (r_hi * 77371252455336267181195264) * 3) 77371252455336267181195263) r_hi)
            (evmShl 86 (evmAnd rem 77371252455336267181195263))))
    have hus_rw :
        us =
          evmOr
            (evmLt (evmShr (evmAnd (evmAnd 86 255) 255) ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3))
                (evmShr (evmAnd (evmAnd 86 255) 255) rem))
            (evmAnd
              (evmEq (evmShr (evmAnd (evmAnd 86 255) 255) ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3))
                  (evmShr (evmAnd (evmAnd 86 255) 255) rem))
              (evmLt
                (evmMul (evmAnd ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) 77371252455336267181195263) r_hi)
                (evmShl (evmAnd (evmAnd 86 255) 255) (evmAnd rem 77371252455336267181195263)))) := by
      unfold us
      simp [pow86_lit, qc_const_86]
    have h_us_le : us ≤ 1 := by
      rw [hus_rw]
      exact qc_undershoot_le_one ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) rem r_hi
    have h_rloc_wm : r_lo - c < WORD_MOD := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hr_lo
    have h_rloc_wm' :
        r_lo - r_lo * r_lo / (r_hi * 2 ^ 86) < WORD_MOD := by
      simpa [c] using h_rloc_wm
    have h_us_wm : us < WORD_MOD := by
      unfold WORD_MOD
      omega
    have h_inner : r_lo - c + us < WORD_MOD := by
      unfold WORD_MOD
      omega
    have h_inner' : r_lo - r_lo * r_lo / (r_hi * 2 ^ 86) + us < WORD_MOD := by
      simpa [c] using h_inner
    have h_add_inner :
        evmAdd (r_lo - r_lo * r_lo / (r_hi * 2 ^ 86)) us =
        r_lo - r_lo * r_lo / (r_hi * 2 ^ 86) + us := by
      exact evmAdd_eq' _ _ h_rloc_wm' h_us_wm h_inner'
    have h_add_outer :
        evmAdd (r_hi * 77371252455336267181195264)
            (r_lo - r_lo * r_lo / (r_hi * 77371252455336267181195264) + us) =
        r_hi * 77371252455336267181195264 +
            (r_lo - r_lo * r_lo / (r_hi * 77371252455336267181195264) + us) := by
      simpa [pow86_lit] using
        (evmAdd_eq' _ _ hR_wm h_inner' (by unfold WORD_MOD; omega))
    rw [h_add_inner, h_add_outer, hsub_lit]
    refine ⟨by
        simpa [pow86_lit, c] using
          (show r_hi * 77371252455336267181195264 + r_lo ≤
              r_hi * 77371252455336267181195264 +
                (r_lo - c +
                  evmOr
                    (evmLt (evmShr 86 (r_lo * r_lo % (r_hi * 77371252455336267181195264) * 3)) (evmShr 86 rem))
                    (evmAnd
                      (evmEq (evmShr 86 (r_lo * r_lo % (r_hi * 77371252455336267181195264) * 3)) (evmShr 86 rem))
                      (evmLt
                        (evmMul (evmAnd (r_lo * r_lo % (r_hi * 77371252455336267181195264) * 3) 77371252455336267181195263) r_hi)
                        (evmShl 86 (evmAnd rem 77371252455336267181195263))))) + c by
            omega),
      by
        simpa [pow86_lit, c] using
          (show r_hi * 77371252455336267181195264 +
              (r_lo - c +
                evmOr
                  (evmLt (evmShr 86 (r_lo * r_lo % (r_hi * 77371252455336267181195264) * 3)) (evmShr 86 rem))
                  (evmAnd
                    (evmEq (evmShr 86 (r_lo * r_lo % (r_hi * 77371252455336267181195264) * 3)) (evmShr 86 rem))
                    (evmLt
                      (evmMul (evmAnd (r_lo * r_lo % (r_hi * 77371252455336267181195264) * 3) 77371252455336267181195263) r_hi)
                      (evmShl 86 (evmAnd rem 77371252455336267181195263))))) ≤
              r_hi * 77371252455336267181195264 + r_lo - c + 1 by
            omega),
      by unfold WORD_MOD; omega⟩
  · -- Case c ≤ 1: no undershoot, result = R + (r_lo - c)
    have hnotgt_lit : ¬ 1 < r_lo * r_lo / (r_hi * 77371252455336267181195264) := by
      simpa [c, pow86_lit] using hcgt
    have hsub_lit :
        r_lo - r_lo * r_lo / (r_hi * 77371252455336267181195264) = r_lo - c := by
      simp [c, pow86_lit]
    simp [pow86_lit, hnotgt_lit]
    have h_rloc_wm : r_lo - c < WORD_MOD := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hr_lo
    have h_rloc_wm' :
        r_lo - r_lo * r_lo / (r_hi * 2 ^ 86) < WORD_MOD := by
      simpa [c] using h_rloc_wm
    have h_add_outer :
        evmAdd (r_hi * 77371252455336267181195264)
            (r_lo - r_lo * r_lo / (r_hi * 77371252455336267181195264)) =
        r_hi * 77371252455336267181195264 +
            (r_lo - r_lo * r_lo / (r_hi * 77371252455336267181195264)) := by
      simpa [pow86_lit] using
        (evmAdd_eq' _ _ hR_wm h_rloc_wm' (by unfold WORD_MOD; omega))
    rw [h_add_outer, hsub_lit]
    refine ⟨by simpa [pow86_lit, c] using (show r_hi * 77371252455336267181195264 + r_lo ≤ r_hi * 77371252455336267181195264 + (r_lo - c) + c by omega),
      by simpa [pow86_lit, c] using (show r_hi * 77371252455336267181195264 + (r_lo - c) ≤ r_hi * 77371252455336267181195264 + r_lo - c + 1 by omega),
      by unfold WORD_MOD; omega⟩

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
  obtain ⟨_, _, hR_wm, _, _, hc_le, _, _, _,
          hR_eq, hSq_eq, hC_eq, hCR_eq, hResid_eq,
          _, _, hEps3_eq, hSub_eq, hGt_eq⟩ :=
    qc_evm_setup r_hi r_lo hr_hi hr_lo hr_hi_pos hr_hi_bound hr_lo_bound
  let c := r_lo * r_lo / (r_hi * 2 ^ 86)
  have hR_eq_lit : evmShl 86 r_hi = r_hi * 2 ^ 86 := by
    rw [evmShl_eq' 86 r_hi (by omega) hr_hi]
    exact Nat.mod_eq_of_lt hR_wm
  -- Unfold and simplify
  unfold model_cbrtQuadraticCorrection_evm
  simp only [u256_id' r_hi hr_hi, u256_id' r_lo hr_lo, u256_id' rem hrem,
             hR_eq_lit, hSq_eq, hC_eq, hCR_eq, hResid_eq, hEps3_eq, hSub_eq, hGt_eq]
  -- c ≤ 1: the if-branch is NOT taken
  have hcgt : ¬c > 1 := by omega
  have hnotgt_lit : ¬ 1 < r_lo * r_lo / (r_hi * 77371252455336267181195264) := by
    simpa [c, pow86_lit] using hcgt
  have hsub_lit :
      r_lo - r_lo * r_lo / (r_hi * 77371252455336267181195264) = r_lo - c := by
    simp [c, pow86_lit]
  simp [pow86_lit, hnotgt_lit]
  have h_rloc_wm : r_lo - c < WORD_MOD := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hr_lo
  have h_rloc_wm' :
      r_lo - r_lo * r_lo / (r_hi * 2 ^ 86) < WORD_MOD := by
    simpa [c] using h_rloc_wm
  have h_add_outer :
      evmAdd (r_hi * 77371252455336267181195264)
          (r_lo - r_lo * r_lo / (r_hi * 77371252455336267181195264)) =
      r_hi * 77371252455336267181195264 +
          (r_lo - r_lo * r_lo / (r_hi * 77371252455336267181195264)) := by
    simpa [pow86_lit] using
      (evmAdd_eq' _ _ hR_wm h_rloc_wm' (by unfold WORD_MOD; omega))
  rw [h_add_outer, hsub_lit]
  have hcorr_le :
      r_lo * r_lo / (r_hi * 77371252455336267181195264) ≤ r_lo := by
    simpa [c, pow86_lit] using hc_le
  have hrhs_assoc :
    r_hi * 77371252455336267181195264 + r_lo -
        r_lo * r_lo / (r_hi * 77371252455336267181195264) =
      r_hi * 77371252455336267181195264 +
        (r_lo - r_lo * r_lo / (r_hi * 77371252455336267181195264)) := by
    simpa using (Nat.add_sub_assoc hcorr_le (r_hi * 77371252455336267181195264))
  rw [hrhs_assoc, hsub_lit]

/-- Standalone QC bridge for the `c > 1`, `check = 0` branch: if the model
    returns exactly `r_qc`, the Karatsuba remainder is bounded by the scaled
    epsilon term plus the `R - r_hi^2` slack coming from `r_hi < 2^86`. -/
theorem model_cbrtQuadraticCorrection_evm_rem_bound_when_c_gt1_exact
    (r_hi r_lo rem : Nat)
    (hr_hi : r_hi < WORD_MOD) (hr_lo : r_lo < WORD_MOD) (hrem : rem < WORD_MOD)
    (hr_hi_pos : 2 ≤ r_hi)
    (hr_hi_bound : r_hi < 2 ^ 85)
    (hr_lo_bound : r_lo < 2 ^ 87)
    (hrem_small : rem < 3 * (r_hi * r_hi))
    (hc_gt1 : r_lo * r_lo / (r_hi * 2 ^ 86) > 1)
    (hr_exact : model_cbrtQuadraticCorrection_evm r_hi r_lo rem =
      r_hi * 2 ^ 86 + r_lo - r_lo * r_lo / (r_hi * 2 ^ 86)) :
    let R := r_hi * 2 ^ 86
    let ε := r_lo * r_lo % R
    rem * 2 ^ 172 ≤ 3 * R * (ε + R - r_hi * r_hi) := by
  simp only
  obtain ⟨hR_ge, hR_lt, hR_wm, hR_pos, hr_lo_sq_wm, hc_le, _,
          hc_wm, _, hR_eq, hSq_eq, hC_eq, hCR_eq, hResid_eq,
          hmod_lt, heps3_wm, hEps3_eq, hSub_eq, hGt_eq⟩ :=
    qc_evm_setup r_hi r_lo hr_hi hr_lo hr_hi_pos hr_hi_bound hr_lo_bound
  let c := r_lo * r_lo / (r_hi * 2 ^ 86)
  have hR_eq_lit : evmShl 86 r_hi = r_hi * 2 ^ 86 := by
    rw [evmShl_eq' 86 r_hi (by omega) hr_hi]
    exact Nat.mod_eq_of_lt hR_wm
  have hShr_eps3 : evmShr (evmAnd (evmAnd 86 255) 255)
      ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) =
      ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) / 2 ^ 86 := by
    rw [qc_const_86, evmShr_eq' 86 _ (by omega) heps3_wm]
  have hShr_eps3_lit : evmShr 86 ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) =
      ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) / 2 ^ 86 := by
    simpa using hShr_eps3
  have hShr_rem : evmShr (evmAnd (evmAnd 86 255) 255) rem = rem / 2 ^ 86 := by
    rw [qc_const_86, evmShr_eq' 86 rem (by omega) hrem]
  have hShr_rem_lit : evmShr 86 rem = rem / 2 ^ 86 := by
    simpa using hShr_rem
  have heps3_hi_wm : ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) / 2 ^ 86 < WORD_MOD :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) heps3_wm
  have hrem_hi_wm : rem / 2 ^ 86 < WORD_MOD := by
    unfold WORD_MOD
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hrem
  have hLt_hi : evmLt (((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) / 2 ^ 86) (rem / 2 ^ 86) =
      if ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) / 2 ^ 86 < rem / 2 ^ 86 then 1 else 0 :=
    evmLt_eq' _ _ heps3_hi_wm hrem_hi_wm
  have hEq_hi : evmEq (((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) / 2 ^ 86) (rem / 2 ^ 86) =
      if ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) / 2 ^ 86 = rem / 2 ^ 86 then 1 else 0 :=
    evmEq_eq' _ _ heps3_hi_wm hrem_hi_wm
  have hAnd_eps3 : evmAnd ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) 77371252455336267181195263 =
      ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) % 2 ^ 86 :=
    evmAnd_mask86_eq_mod _ heps3_wm
  have hAnd_rem : evmAnd rem 77371252455336267181195263 = rem % 2 ^ 86 :=
    evmAnd_mask86_eq_mod _ hrem
  have heps3_lo_wm : ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) % 2 ^ 86 < WORD_MOD := by
    unfold WORD_MOD
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos 86)) (by omega)
  have hrem_lo_wm : rem % 2 ^ 86 < WORD_MOD := by
    unfold WORD_MOD
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos 86)) (by omega)
  have hMul_lo : evmMul (((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) % 2 ^ 86) r_hi =
      ((((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) % 2 ^ 86) * r_hi) % WORD_MOD :=
    evmMul_eq' _ _ heps3_lo_wm hr_hi
  have hprod_eps3_wm :
      (((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) % 2 ^ 86) * r_hi < WORD_MOD := by
    calc (((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) % 2 ^ 86) * r_hi
        < 2 ^ 86 * r_hi := Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos 86)) (by omega)
      _ < 2 ^ 86 * 2 ^ 85 := Nat.mul_lt_mul_of_pos_left hr_hi_bound (Nat.two_pow_pos 86)
      _ = 2 ^ 171 := by rw [← Nat.pow_add]
    unfold WORD_MOD
    omega
  rw [Nat.mod_eq_of_lt hprod_eps3_wm] at hMul_lo
  have hShl_rem : evmShl (evmAnd (evmAnd 86 255) 255) (rem % 2 ^ 86) =
      (rem % 2 ^ 86) * 2 ^ 86 := by
    rw [qc_const_86, evmShl_eq' 86 (rem % 2 ^ 86) (by omega) hrem_lo_wm]
    have : (rem % 2 ^ 86) * 2 ^ 86 < WORD_MOD := by
      calc (rem % 2 ^ 86) * 2 ^ 86
          < 2 ^ 86 * 2 ^ 86 := Nat.mul_lt_mul_of_pos_right
            (Nat.mod_lt _ (Nat.two_pow_pos 86)) (Nat.two_pow_pos 86)
        _ = 2 ^ 172 := by rw [← Nat.pow_add]
      unfold WORD_MOD
      omega
    exact Nat.mod_eq_of_lt this
  have hShl_rem_lit : evmShl 86 (rem % 2 ^ 86) = (rem % 2 ^ 86) * 2 ^ 86 := by
    simpa using hShl_rem
  have hprod_rem_wm : (rem % 2 ^ 86) * 2 ^ 86 < WORD_MOD := by
    calc (rem % 2 ^ 86) * 2 ^ 86
        < 2 ^ 86 * 2 ^ 86 := Nat.mul_lt_mul_of_pos_right
          (Nat.mod_lt _ (Nat.two_pow_pos 86)) (Nat.two_pow_pos 86)
      _ = 2 ^ 172 := by rw [← Nat.pow_add]
    unfold WORD_MOD
    omega
  have hLt_lo : evmLt ((((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) % 2 ^ 86) * r_hi)
      ((rem % 2 ^ 86) * 2 ^ 86) =
      if (((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) % 2 ^ 86) * r_hi < (rem % 2 ^ 86) * 2 ^ 86
      then 1 else 0 :=
    evmLt_eq' _ _ hprod_eps3_wm hprod_rem_wm
  unfold model_cbrtQuadraticCorrection_evm at hr_exact
  simp only [u256_id' r_hi hr_hi, u256_id' r_lo hr_lo, u256_id' rem hrem,
             hR_eq_lit, hSq_eq, hC_eq, hCR_eq, hResid_eq, hEps3_eq, hSub_eq, hGt_eq] at hr_exact
  have hcgt_lit : 1 < r_lo * r_lo / (r_hi * 77371252455336267181195264) := by
    simpa [c, pow86_lit] using hc_gt1
  have hsub_lit :
      r_lo - r_lo * r_lo / (r_hi * 77371252455336267181195264) = r_lo - c := by
    simp [c, pow86_lit]
  simp [pow86_lit, hcgt_lit] at hr_exact
  rw [hShr_eps3_lit, hShr_rem_lit, hLt_hi, hAnd_eps3, hAnd_rem, hMul_lo, hShl_rem_lit, hLt_lo,
      hEq_hi] at hr_exact
  rw [evmAnd_eq'
      (if ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) / 2 ^ 86 = rem / 2 ^ 86 then 1 else 0)
      (if (((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) % 2 ^ 86) * r_hi < (rem % 2 ^ 86) * 2 ^ 86
        then 1 else 0)
      (by split <;> unfold WORD_MOD <;> omega)
      (by split <;> unfold WORD_MOD <;> omega)] at hr_exact
  rw [evmOr_eq'
      (if ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) / 2 ^ 86 < rem / 2 ^ 86 then 1 else 0)
      ((if ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) / 2 ^ 86 = rem / 2 ^ 86 then 1 else 0) &&&
        (if (((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) % 2 ^ 86) * r_hi < (rem % 2 ^ 86) * 2 ^ 86
          then 1 else 0))
      (by split <;> unfold WORD_MOD <;> omega)
      (by
        have := and_le_one _ _
          (by split <;> omega :
            (if ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) / 2 ^ 86 = rem / 2 ^ 86 then 1 else 0) ≤ 1)
          (by split <;> omega :
            (if (((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) % 2 ^ 86) * r_hi < (rem % 2 ^ 86) * 2 ^ 86
              then 1 else 0) ≤ 1)
        unfold WORD_MOD
        omega)] at hr_exact
  generalize hcheck :
      (if ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) / 2 ^ 86 < rem / 2 ^ 86 then 1 else 0) |||
      ((if ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) / 2 ^ 86 = rem / 2 ^ 86 then 1 else 0) &&&
       (if (((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) % 2 ^ 86) * r_hi < (rem % 2 ^ 86) * 2 ^ 86
        then 1 else 0)) = check at hr_exact
  have hcheck_le : check ≤ 1 := by
    rw [← hcheck]
    exact or_le_one _ _
      (by split <;> omega)
      (and_le_one _ _
        (by split <;> omega) (by split <;> omega))
  have hcheck_wm : check < WORD_MOD := by
    unfold WORD_MOD
    omega
  have h_rloc_wm : r_lo - c < WORD_MOD := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hr_lo
  have h_inner : r_lo - c + check < WORD_MOD := by
    have hc_ge2 : 2 ≤ c := hc_gt1
    unfold WORD_MOD
    omega
  rw [hsub_lit] at hr_exact
  rw [evmAdd_eq' _ _ h_rloc_wm hcheck_wm h_inner,
      evmAdd_eq' _ _ hR_wm h_inner (by unfold WORD_MOD; omega)] at hr_exact
  have hr_exact_nat :
      r_hi * 2 ^ 86 + (r_lo - c + check) = r_hi * 2 ^ 86 + r_lo - c := by
    simpa [pow86_lit, c] using hr_exact
  have hcheck_eq_zero : check = 0 := by
    omega
  have hcases := qc_check_zero_cases ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) rem r_hi (by
    simpa [hcheck] using hcheck_eq_zero)
  have hr_hi_le : r_hi ≤ 2 ^ 86 := by
    exact Nat.le_trans (Nat.le_of_lt hr_hi_bound)
      (Nat.pow_le_pow_right (by omega) (by omega : 85 ≤ 86))
  have hrem_le_eps3 : rem ≤ ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) := by
    rcases hcases with h_hi_lt | ⟨h_hi_eq, h_lo_le⟩
    · exact Nat.le_of_lt (div_lt_implies_lt rem _ h_hi_lt)
    · exact split_limb_le_implies_le rem ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) r_hi
        hr_hi_le h_hi_eq h_lo_le
  have hrem_small_le : rem ≤ 3 * (r_hi * r_hi) := Nat.le_of_lt hrem_small
  have hpow_split :
      2 ^ 172 = r_hi * 2 ^ 86 + 2 ^ 86 * (2 ^ 86 - r_hi) := by
    calc 2 ^ 172 = 2 ^ 86 * 2 ^ 86 := by rw [show (172 : Nat) = 86 + 86 from rfl, Nat.pow_add]
      _ = 2 ^ 86 * (r_hi + (2 ^ 86 - r_hi)) := by rw [Nat.add_sub_of_le hr_hi_le]
      _ = 2 ^ 86 * r_hi + 2 ^ 86 * (2 ^ 86 - r_hi) := by rw [Nat.mul_add]
      _ = r_hi * 2 ^ 86 + 2 ^ 86 * (2 ^ 86 - r_hi) := by rw [Nat.mul_comm]
  have htarget :
      (((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) * (r_hi * 2 ^ 86) +
        (3 * (r_hi * r_hi)) * (2 ^ 86 * (2 ^ 86 - r_hi))) =
        3 * (r_hi * 2 ^ 86) * ((r_lo * r_lo % (r_hi * 2 ^ 86)) + (r_hi * 2 ^ 86 - r_hi * r_hi)) := by
    have hgap : r_hi * 2 ^ 86 - r_hi * r_hi = r_hi * (2 ^ 86 - r_hi) := by
      rw [Nat.mul_sub_left_distrib]
    rw [hgap]
    have hfirst :
        ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) * (r_hi * 2 ^ 86) =
          3 * (r_hi * 2 ^ 86) * (r_lo * r_lo % (r_hi * 2 ^ 86)) := by
      ac_rfl
    have hsecond :
        (3 * (r_hi * r_hi)) * (2 ^ 86 * (2 ^ 86 - r_hi)) =
          3 * (r_hi * 2 ^ 86) * (r_hi * (2 ^ 86 - r_hi)) := by
      ac_rfl
    rw [hfirst, hsecond, ← Nat.mul_add]
  have hr_sq_le_R : r_hi * r_hi ≤ r_hi * 2 ^ 86 := by
    exact Nat.mul_le_mul_left _ hr_hi_le
  calc rem * 2 ^ 172
      = rem * (r_hi * 2 ^ 86) + rem * (2 ^ 86 * (2 ^ 86 - r_hi)) := by
          rw [hpow_split, Nat.mul_add]
    _ ≤ ((r_lo * r_lo % (r_hi * 2 ^ 86)) * 3) * (r_hi * 2 ^ 86) +
        (3 * (r_hi * r_hi)) * (2 ^ 86 * (2 ^ 86 - r_hi)) := by
          exact Nat.add_le_add
            (Nat.mul_le_mul_right _ hrem_le_eps3)
            (Nat.mul_le_mul_right _ hrem_small_le)
    _ = 3 * (r_hi * 2 ^ 86) *
        ((r_lo * r_lo % (r_hi * 2 ^ 86)) + (r_hi * 2 ^ 86 - r_hi * r_hi)) := htarget
    _ = 3 * (r_hi * 2 ^ 86) *
        (r_lo * r_lo % (r_hi * 2 ^ 86) + r_hi * 2 ^ 86 - r_hi * r_hi) := by
          rw [show (r_lo * r_lo % (r_hi * 2 ^ 86)) + (r_hi * 2 ^ 86 - r_hi * r_hi) =
              r_lo * r_lo % (r_hi * 2 ^ 86) + r_hi * 2 ^ 86 - r_hi * r_hi from by
            simpa using (Nat.add_sub_assoc hr_sq_le_R (r_lo * r_lo % (r_hi * 2 ^ 86))).symm]


end Cbrt512Spec
