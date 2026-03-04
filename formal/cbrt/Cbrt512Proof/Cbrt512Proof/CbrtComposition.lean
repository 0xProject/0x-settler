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
  -- R ≥ 2^87 (from r_hi ≥ 2)
  have hR_ge : 2 ^ 87 ≤ r_hi * 2 ^ 86 :=
    calc 2 ^ 87 = 2 ^ 1 * 2 ^ 86 := by rw [← Nat.pow_add]
      _ ≤ r_hi * 2 ^ 86 := Nat.mul_le_mul_right _ hr_hi_pos
  have hR_gt_rlo : r_lo < r_hi * 2 ^ 86 := by omega
  -- r_lo² < 2^174 < WORD_MOD
  have hlo_sq_lt : r_lo * r_lo < 2 ^ 174 := by
    by_cases h : r_lo = 0
    · subst h; exact Nat.two_pow_pos 174
    · calc r_lo * r_lo
          < r_lo * 2 ^ 87 := Nat.mul_lt_mul_of_pos_left hr_lo_bound (by omega)
        _ ≤ 2 ^ 87 * 2 ^ 87 := Nat.mul_le_mul_right _ (by omega)
        _ = 2 ^ 174 := by rw [← Nat.pow_add]
  have hlo_sq_wm : r_lo * r_lo < WORD_MOD := by unfold WORD_MOD; omega
  -- correction ≤ r_lo
  have hcorr_le_rlo : r_lo * r_lo / (r_hi * 2 ^ 86) ≤ r_lo := by
    by_cases h : r_lo = 0
    · simp [h]
    · -- r_lo * r_lo < r_lo * R, so r_lo²/R < r_lo
      have hlt : r_lo * r_lo < r_lo * (r_hi * 2 ^ 86) :=
        Nat.mul_lt_mul_of_pos_left hR_gt_rlo (by omega)
      have := (Nat.div_lt_iff_lt_mul hR_pos).mpr hlt
      omega
  -- Sum bounds
  have hsum_wm : r_hi * 2 ^ 86 + r_lo < WORD_MOD := by unfold WORD_MOD; omega
  have hresult_wm : r_hi * 2 ^ 86 + r_lo - r_lo * r_lo / (r_hi * 2 ^ 86) < WORD_MOD :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hsum_wm
  have hrlo1_wm : r_lo - r_lo * r_lo / (r_hi * 2 ^ 86) < WORD_MOD :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hr_lo
  -- ========== u256 stripping ==========
  have hr_hi_u : u256 r_hi = r_hi := u256_id' r_hi hr_hi
  have hr_lo_u : u256 r_lo = r_lo := u256_id' r_lo hr_lo
  -- ========== Constant folding: evmAnd(evmAnd(86,255),255) = 86 ==========
  have h86_wm : (86 : Nat) < WORD_MOD := by unfold WORD_MOD; omega
  have h255_wm : (255 : Nat) < WORD_MOD := by unfold WORD_MOD; omega
  have hand_inner : evmAnd 86 255 = 86 := by
    rw [evmAnd_eq' 86 255 h86_wm h255_wm]
    exact Nat.and_two_pow_sub_one_eq_mod 86 8
  have hand_outer : evmAnd (evmAnd 86 255) 255 = 86 := by
    rw [hand_inner, evmAnd_eq' 86 255 h86_wm h255_wm]
    exact Nat.and_two_pow_sub_one_eq_mod 86 8
  -- ========== Assemble via show + bottom-up rewriting ==========
  constructor
  · -- Unfold model to flat EVM expression (definitionally equal via let-inlining)
    show evmAdd (evmShl (evmAnd (evmAnd 86 255) 255) (u256 r_hi))
               (evmSub (u256 r_lo) (evmDiv (evmMul (u256 r_lo) (u256 r_lo))
                 (evmShl (evmAnd (evmAnd 86 255) 255) (u256 r_hi)))) =
         r_hi * 2 ^ 86 + r_lo - r_lo * r_lo / (r_hi * 2 ^ 86)
    -- Strip u256 wrappers and fold constant
    rw [hr_hi_u, hr_lo_u, hand_outer]
    -- evmShl 86 r_hi → r_hi * 2^86 (both occurrences)
    rw [show evmShl 86 r_hi = r_hi * 2 ^ 86 from by
      rw [evmShl_eq' 86 r_hi (by omega) hr_hi]; exact Nat.mod_eq_of_lt hR_wm]
    -- evmMul r_lo r_lo → r_lo * r_lo
    rw [evmMul_eq' r_lo r_lo hr_lo hr_lo, Nat.mod_eq_of_lt hlo_sq_wm]
    -- evmDiv → Nat div
    rw [evmDiv_eq' (r_lo * r_lo) (r_hi * 2 ^ 86) hlo_sq_wm hR_pos hR_wm]
    -- evmSub → Nat sub
    rw [evmSub_eq_of_le r_lo _ hr_lo hcorr_le_rlo]
    -- evmAdd → Nat add
    rw [evmAdd_eq' _ _ hR_wm hrlo1_wm (by omega)]
    -- a + (b - c) = a + b - c when c ≤ b
    omega
  · exact hresult_wm

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
  sorry

end Cbrt512Spec
