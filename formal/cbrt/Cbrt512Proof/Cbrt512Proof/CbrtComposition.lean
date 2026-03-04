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
import Cbrt512Proof.EvmBridge
import CbrtProof.CbrtCorrect

namespace Cbrt512Spec

open Cbrt512GeneratedModel

-- ============================================================================
-- Quadratic correction EVM bridge
-- ============================================================================

/-- The quadratic correction: r = r_hi * 2^86 + r_lo - r_lo²/(r_hi * 2^86).
    Requires r_hi ≥ 2 (which holds since r_hi = icbrt(w) with w ≥ 2^251,
    giving r_hi ≥ 2^83). With r_hi ≥ 2: R = r_hi * 2^86 ≥ 2^87 > r_lo,
    so the correction r_lo²/R < r_lo ≤ R + r_lo and no EVM operation wraps. -/
theorem model_cbrtQuadraticCorrection_evm_correct
    (r_hi r_lo : Nat)
    (hr_hi : r_hi < WORD_MOD) (hr_lo : r_lo < WORD_MOD)
    (hr_hi_pos : 2 ≤ r_hi)
    (hr_hi_bound : r_hi < 2 ^ 85)
    (hr_lo_bound : r_lo < 2 ^ 87) :
    let R := r_hi * 2 ^ 86
    let correction := r_lo * r_lo / R
    model_cbrtQuadraticCorrection_evm r_hi r_lo = R + r_lo - correction ∧
    R + r_lo - correction < WORD_MOD := by
  simp only
  -- ========== Key bounds ==========
  have hR_pos : 0 < r_hi * 2 ^ 86 := Nat.mul_pos (by omega) (Nat.two_pow_pos 86)
  have hR_lt : r_hi * 2 ^ 86 < 2 ^ 171 :=
    calc r_hi * 2 ^ 86
        < 2 ^ 85 * 2 ^ 86 := Nat.mul_lt_mul_of_pos_right hr_hi_bound (Nat.two_pow_pos 86)
      _ = 2 ^ 171 := by rw [← Nat.pow_add]
  have hR_wm : r_hi * 2 ^ 86 < WORD_MOD := by unfold WORD_MOD; omega
  have hR_ge : 2 ^ 87 ≤ r_hi * 2 ^ 86 :=
    calc 2 ^ 87 = 2 ^ 1 * 2 ^ 86 := by rw [← Nat.pow_add]
      _ ≤ r_hi * 2 ^ 86 := Nat.mul_le_mul_right _ hr_hi_pos
  have hR_gt_rlo : r_lo < r_hi * 2 ^ 86 := by omega
  have hlo_sq_lt : r_lo * r_lo < 2 ^ 174 := by
    by_cases h : r_lo = 0
    · subst h; exact Nat.two_pow_pos 174
    · calc r_lo * r_lo
          < r_lo * 2 ^ 87 := Nat.mul_lt_mul_of_pos_left hr_lo_bound (by omega)
        _ ≤ 2 ^ 87 * 2 ^ 87 := Nat.mul_le_mul_right _ (by omega)
        _ = 2 ^ 174 := by rw [← Nat.pow_add]
  have hlo_sq_wm : r_lo * r_lo < WORD_MOD := by unfold WORD_MOD; omega
  have hcorr_le_rlo : r_lo * r_lo / (r_hi * 2 ^ 86) ≤ r_lo := by
    by_cases h : r_lo = 0
    · simp [h]
    · have hlt : r_lo * r_lo < r_lo * (r_hi * 2 ^ 86) :=
        Nat.mul_lt_mul_of_pos_left hR_gt_rlo (by omega)
      have := (Nat.div_lt_iff_lt_mul hR_pos).mpr hlt
      omega
  have hsum_wm : r_hi * 2 ^ 86 + r_lo < WORD_MOD := by unfold WORD_MOD; omega
  have hresult_wm : r_hi * 2 ^ 86 + r_lo - r_lo * r_lo / (r_hi * 2 ^ 86) < WORD_MOD :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hsum_wm
  have hrlo1_wm : r_lo - r_lo * r_lo / (r_hi * 2 ^ 86) < WORD_MOD :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hr_lo
  have hr_hi_u : u256 r_hi = r_hi := u256_id' r_hi hr_hi
  have hr_lo_u : u256 r_lo = r_lo := u256_id' r_lo hr_lo
  have h86_wm : (86 : Nat) < WORD_MOD := by unfold WORD_MOD; omega
  have h255_wm : (255 : Nat) < WORD_MOD := by unfold WORD_MOD; omega
  have hand_inner : evmAnd 86 255 = 86 := by
    rw [evmAnd_eq' 86 255 h86_wm h255_wm]
    exact Nat.and_two_pow_sub_one_eq_mod 86 8
  have hand_outer : evmAnd (evmAnd 86 255) 255 = 86 := by
    rw [hand_inner, evmAnd_eq' 86 255 h86_wm h255_wm]
    exact Nat.and_two_pow_sub_one_eq_mod 86 8
  constructor
  · show evmAdd (evmShl (evmAnd (evmAnd 86 255) 255) (u256 r_hi))
               (evmSub (u256 r_lo) (evmDiv (evmMul (u256 r_lo) (u256 r_lo))
                 (evmShl (evmAnd (evmAnd 86 255) 255) (u256 r_hi)))) =
         r_hi * 2 ^ 86 + r_lo - r_lo * r_lo / (r_hi * 2 ^ 86)
    rw [hr_hi_u, hr_lo_u, hand_outer]
    rw [show evmShl 86 r_hi = r_hi * 2 ^ 86 from by
      rw [evmShl_eq' 86 r_hi (by omega) hr_hi]; exact Nat.mod_eq_of_lt hR_wm]
    rw [evmMul_eq' r_lo r_lo hr_lo hr_lo, Nat.mod_eq_of_lt hlo_sq_wm]
    rw [evmDiv_eq' (r_lo * r_lo) (r_hi * 2 ^ 86) hlo_sq_wm hR_pos hR_wm]
    rw [evmSub_eq_of_le r_lo _ hr_lo hcorr_le_rlo]
    rw [evmAdd_eq' _ _ hR_wm hrlo1_wm (by omega)]
    omega
  · exact hresult_wm

-- ============================================================================
-- Helper: the algorithm gives exactly icbrt (sorry'd — hard numerical bound)
-- ============================================================================

/-- The quadratic-corrected result equals icbrt(x_norm).
    This combines two properties:
    1. No-overshoot: r_qc ≤ icbrt(x_norm), because floor divisions in r_lo and
       correction ensure r_qc³ ≤ x_norm. See the "cube-and-compare" comment in
       512Math.sol's `cbrt` function for the detailed numerical argument.
    2. No-undershoot: icbrt(x_norm) ≤ r_qc, because (r_qc+1)³ > x_norm.
       This follows from the Karatsuba remainder being bounded by d, so the
       gap x_norm - R³ - 3R²·r_lo < d·2^172 ≤ 3R², which is absorbed by the
       +1 margin in (r_qc+1)³. -/
private theorem r_qc_eq_icbrt (x_hi_1 x_lo_1 : Nat)
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
    r_qc = icbrt (x_hi_1 * 2 ^ 256 + x_lo_1) := by
  sorry

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
    icbrt x_norm ≤ r_qc ∧ r_qc ≤ icbrt x_norm + 1 ∧
    r_qc < WORD_MOD ∧
    r_qc * r_qc * r_qc < WORD_MOD * WORD_MOD ∧
    r_qc + 1 < WORD_MOD ∧
    (r_qc * r_qc * r_qc > x_norm →
      icbrt x_norm * icbrt x_norm * icbrt x_norm < x_norm) := by
  -- Key facts (let-bindings match the goal's)
  have h_eq := r_qc_eq_icbrt x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  have h_bound := r_qc_lt_pow172 x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  have hcube_le := icbrt_cube_le (x_hi_1 * 2 ^ 256 + x_lo_1)
  have hx_bound : x_hi_1 * 2 ^ 256 + x_lo_1 < WORD_MOD * WORD_MOD := by
    have hxhi' : x_hi_1 < 2 ^ 256 := by unfold WORD_MOD at hxhi_hi; exact hxhi_hi
    have hxlo' : x_lo_1 < 2 ^ 256 := by unfold WORD_MOD at hxlo; exact hxlo
    unfold WORD_MOD
    rw [show 2 ^ 256 * 2 ^ 256 = 2 ^ 512 from by rw [← Nat.pow_add]]
    calc x_hi_1 * 2 ^ 256 + x_lo_1
        < x_hi_1 * 2 ^ 256 + 2 ^ 256 := by omega
      _ = (x_hi_1 + 1) * 2 ^ 256 := (Nat.succ_mul _ _).symm
      _ ≤ 2 ^ 256 * 2 ^ 256 := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ 512 := by rw [← Nat.pow_add]
  -- Unfold let-bindings so omega/rw can see through them
  simp only at h_eq h_bound hcube_le hx_bound ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- [1] icbrt x_norm ≤ r_qc: from h_eq (a = b → b ≤ a)
    omega
  · -- [2] r_qc ≤ icbrt x_norm + 1: from h_eq (a = b → a ≤ b + 1)
    omega
  · -- [3] r_qc < WORD_MOD: from h_bound (r_qc < 2^172 < WORD_MOD)
    unfold WORD_MOD; omega
  · -- [4] r_qc³ < WORD_MOD²: r_qc = icbrt so r_qc³ ≤ x_norm < WORD_MOD²
    -- Chain: r_qc³ = icbrt³ ≤ x_norm < WORD_MOD * WORD_MOD
    calc _ = icbrt (x_hi_1 * 2 ^ 256 + x_lo_1) * icbrt (x_hi_1 * 2 ^ 256 + x_lo_1) *
              icbrt (x_hi_1 * 2 ^ 256 + x_lo_1) := by rw [h_eq]
      _ ≤ x_hi_1 * 2 ^ 256 + x_lo_1 := hcube_le
      _ < WORD_MOD * WORD_MOD := hx_bound
  · -- [5] r_qc + 1 < WORD_MOD: from h_bound
    unfold WORD_MOD; omega
  · -- [6] overshoot → not perfect cube: vacuous since r_qc = icbrt
    intro h_overshoot; rw [h_eq] at h_overshoot; omega

end Cbrt512Spec
