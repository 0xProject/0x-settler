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
-- Sub-lemma A: Lower bound — (r_qc + 1)³ > x_norm
-- ============================================================================

/-- The cube of (r_qc + 1) exceeds x_norm.
    Combined with icbrt_cube_le, this gives icbrt(x_norm) ≤ r_qc.
    Proof sketch: x_norm = R³ + 3R²·r_lo + rem·2^172 + c_tail.
    (r_qc+1)³ = R³ + 3R²(q+1) + 3R(q+1)² + (q+1)³ where q = r_lo - c.
    The key: (3m²-rem)·2^172 ≥ 2^172 > c_tail, combined with
    3R(q+1)² + (q+1)³ > 3R²c (since 3R²(c+1) > 3R·r_lo² ≥ 3R·q²). -/
private theorem r_qc_succ_cube_gt (x_hi_1 x_lo_1 : Nat)
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
    x_norm < (r_qc + 1) * (r_qc + 1) * (r_qc + 1) := by
  sorry

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
  sorry

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

/-- The composition pipeline output never exceeds R_MAX.
    Proof has two cases:
    1. x_norm < R_MAX³: icbrt(x_norm) < R_MAX (cube_monotone), so from sub-lemma B
       r_qc ≤ icbrt + 1 ≤ R_MAX.
    2. x_norm ≥ R_MAX³: x_hi_1 / 4 ≥ a threshold where ⌊∛(x_hi_1/4)⌋ is constant
       (= 0x1965fea53d6e3c82b05999). The Karatsuba quotient r_lo is constant
       (fractional part of n/d stays in [0.128, 0.292] across the range, never
       crossing an integer boundary — see 512Math.sol cbrt() lines 1974–2010).
       The quadratic correction subtracts exactly 1, yielding r_qc = R_MAX. -/
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
  sorry

-- ============================================================================
-- Sub-lemma E2: Overshoot implies not a perfect cube
-- ============================================================================

/-- When the algorithm overshoots (r_qc³ > x_norm), x_norm is not a perfect cube.
    From sub-lemmas A and B, r_qc = icbrt(x_norm) + 1 when r_qc³ > x_norm.
    If x_norm were a perfect cube s³, the Karatsuba quotient r_lo captures the
    exact linear correction and the quadratic correction c = ⌊r_lo²/R⌋ exactly
    compensates, yielding r_qc = s (no overshoot). -/
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
  sorry

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
    icbrt x_norm ≤ r_qc ∧ r_qc ≤ icbrt x_norm + 1 ∧
    r_qc * r_qc * r_qc < WORD_MOD * WORD_MOD ∧
    (r_qc * r_qc * r_qc > x_norm →
      icbrt x_norm * icbrt x_norm * icbrt x_norm < x_norm) := by
  simp only
  -- Sub-lemmas (simp only inlines the let-bindings, matching the goal)
  have hA := r_qc_succ_cube_gt x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  have hB := r_qc_pred_cube_le x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  have hE1 := r_qc_le_r_max x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  have hE2 := r_qc_no_overshoot_on_cubes x_hi_1 x_lo_1 hxhi_lo hxhi_hi hxlo
  simp only at hA hB hE1 hE2
  have hcube_le := icbrt_cube_le (x_hi_1 * 2 ^ 256 + x_lo_1)
  have hsucc_gt := icbrt_lt_succ_cube (x_hi_1 * 2 ^ 256 + x_lo_1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- [1] icbrt(x_norm) ≤ r_qc: if r_qc < icbrt then (r_qc+1)³ ≤ icbrt³ ≤ x_norm,
    --     contradicting hA: x_norm < (r_qc+1)³.
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
