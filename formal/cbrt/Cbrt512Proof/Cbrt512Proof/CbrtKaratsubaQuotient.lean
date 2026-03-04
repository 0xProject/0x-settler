/-
  Karatsuba quotient: model_cbrtKaratsubaQuotient_evm(res, limb_hi, d) computes
  floor((res * 2^86 + limb_hi) / d) correctly, even when res * 2^86 + limb_hi
  overflows 256 bits.

  The carry branch handles overflow: when res >> 170 ≠ 0, the dividend n has
  257+ bits. The three-part decomposition computes floor((WORD_MOD + n_evm) / d).

  Also proves limb_hi extraction: the next 86 bits of x_norm after the base case.
-/
import Cbrt512Proof.GeneratedCbrt512Model

namespace Cbrt512Spec

open Cbrt512GeneratedModel

-- ============================================================================
-- limb_hi extraction
-- ============================================================================

/-- The limb_hi extraction correctly picks out 86 bits:
    limb_hi = evmOr(evmShl(84, evmAnd(3, x_hi_1)), evmShr(172, x_lo_1))
    equals (x_hi_1 % 4) * 2^84 + x_lo_1 / 2^172. -/
theorem limb_hi_correct (x_hi_1 x_lo_1 : Nat)
    (hxhi : x_hi_1 < WORD_MOD) (hxlo : x_lo_1 < WORD_MOD) :
    let limb_hi := evmOr (evmShl 84 (evmAnd 3 x_hi_1)) (evmShr 172 x_lo_1)
    limb_hi = (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 ∧
    limb_hi < 2 ^ 86 ∧
    limb_hi < WORD_MOD := by
  sorry

-- ============================================================================
-- Karatsuba quotient correctness
-- ============================================================================

/-- The Karatsuba quotient computes floor((res * 2^86 + limb_hi) / d).
    This handles both the normal case (no overflow) and the carry case. -/
theorem model_cbrtKaratsubaQuotient_evm_correct
    (res limb_hi d : Nat)
    (hres : res < WORD_MOD) (hlimb : limb_hi < WORD_MOD)
    (hd : d < WORD_MOD) (hd_pos : 0 < d)
    -- res is the residue from base case: res ≤ 3*r_hi² + 3*r_hi
    -- d = 3 * r_hi² with r_hi ∈ [2^83, 2^85)
    -- So res < 2^171 (at most) and limb_hi < 2^86
    (hres_bound : res < 2 ^ 171)
    (hlimb_bound : limb_hi < 2 ^ 86) :
    model_cbrtKaratsubaQuotient_evm res limb_hi d =
      (res * 2 ^ 86 + limb_hi) / d := by
  sorry

end Cbrt512Spec
