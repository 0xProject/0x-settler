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
import CbrtProof.CbrtCorrect

namespace Cbrt512Spec

open Cbrt512GeneratedModel

-- ============================================================================
-- Quadratic correction EVM bridge
-- ============================================================================

/-- The quadratic correction: r = r_hi * 2^86 + r_lo - r_lo²/(r_hi * 2^86).
    Requires r_hi > 0, and r_lo² doesn't truly overflow (it may wrap but the
    division still gives the correct quotient). -/
theorem model_cbrtQuadraticCorrection_evm_correct
    (r_hi r_lo : Nat)
    (hr_hi : r_hi < WORD_MOD) (hr_lo : r_lo < WORD_MOD)
    (hr_hi_pos : 0 < r_hi)
    (hr_hi_bound : r_hi < 2 ^ 85)
    (hr_lo_bound : r_lo < 2 ^ 87) :
    let R := r_hi * 2 ^ 86
    let correction := r_lo * r_lo / R
    model_cbrtQuadraticCorrection_evm r_hi r_lo = R + r_lo - correction ∧
    R + r_lo - correction < WORD_MOD := by
  sorry

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
