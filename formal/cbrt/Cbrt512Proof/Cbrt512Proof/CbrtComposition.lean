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
        (evmLt (evmMul (evmAnd eps3 1237940039285380274899124223) r_hi)
               (evmShl (evmAnd (evmAnd 86 255) 255)
                       (evmAnd rem 1237940039285380274899124223)))) ≤ 1 :=
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
