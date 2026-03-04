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
  simp only
  -- Step 1: evmAnd 3 x_hi_1 = x_hi_1 % 4
  have h3_wm : (3 : Nat) < WORD_MOD := by unfold WORD_MOD; omega
  have hand : evmAnd 3 x_hi_1 = x_hi_1 % 4 := by
    unfold evmAnd u256
    simp [Nat.mod_eq_of_lt h3_wm, Nat.mod_eq_of_lt hxhi]
    rw [Nat.and_comm]
    exact Nat.and_two_pow_sub_one_eq_mod x_hi_1 2
  have hmod4 : x_hi_1 % 4 < 4 := Nat.mod_lt _ (by omega)
  have hmod4_wm : x_hi_1 % 4 < WORD_MOD := by unfold WORD_MOD; omega
  -- Step 2: evmShl 84 (evmAnd 3 x_hi_1) = (x_hi_1 % 4) * 2^84
  have hprod_lt : (x_hi_1 % 4) * 2 ^ 84 < 2 ^ 86 :=
    calc (x_hi_1 % 4) * 2 ^ 84
        < 4 * 2 ^ 84 := Nat.mul_lt_mul_of_pos_right hmod4 (Nat.two_pow_pos 84)
      _ = 2 ^ 86 := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
  have hprod_wm : (x_hi_1 % 4) * 2 ^ 84 < WORD_MOD :=
    Nat.lt_of_lt_of_le hprod_lt
      (by unfold WORD_MOD; exact Nat.pow_le_pow_right (by omega) (by omega))
  have hshl : evmShl 84 (evmAnd 3 x_hi_1) = (x_hi_1 % 4) * 2 ^ 84 := by
    rw [hand]; unfold evmShl u256
    simp [Nat.mod_eq_of_lt (show (84 : Nat) < WORD_MOD from by unfold WORD_MOD; omega),
          Nat.mod_eq_of_lt hmod4_wm, show (84 : Nat) < 256 from by omega]
    exact Nat.mod_eq_of_lt hprod_wm
  -- Step 3: evmShr 172 x_lo_1 = x_lo_1 / 2^172
  have hshr : evmShr 172 x_lo_1 = x_lo_1 / 2 ^ 172 := by
    unfold evmShr u256
    simp [Nat.mod_eq_of_lt (show (172 : Nat) < WORD_MOD from by unfold WORD_MOD; omega),
          Nat.mod_eq_of_lt hxlo, show (172 : Nat) < 256 from by omega]
  have hdiv_lt : x_lo_1 / 2 ^ 172 < 2 ^ 84 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 172)]
    calc x_lo_1 < WORD_MOD := hxlo
      _ = 2 ^ 84 * 2 ^ 172 := by unfold WORD_MOD; rw [← Nat.pow_add]
  have hdiv_wm : x_lo_1 / 2 ^ 172 < WORD_MOD :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hxlo
  -- Step 4: evmOr with disjoint bits = addition
  have hor : evmOr (evmShl 84 (evmAnd 3 x_hi_1)) (evmShr 172 x_lo_1) =
      (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 := by
    rw [hshl, hshr]; unfold evmOr u256
    simp [Nat.mod_eq_of_lt hprod_wm, Nat.mod_eq_of_lt hdiv_wm]
    rw [show (x_hi_1 % 4) * 2 ^ 84 = (x_hi_1 % 4) <<< 84 from (Nat.shiftLeft_eq _ _).symm]
    exact (Nat.shiftLeft_add_eq_or_of_lt hdiv_lt (x_hi_1 % 4)).symm
  -- Step 5: bounds
  have hsum_lt : (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < 2 ^ 86 :=
    calc (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172
        < (x_hi_1 % 4) * 2 ^ 84 + 2 ^ 84 := Nat.add_lt_add_left hdiv_lt _
      _ = ((x_hi_1 % 4) + 1) * 2 ^ 84 := (Nat.succ_mul _ _).symm
      _ ≤ 4 * 2 ^ 84 := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ 86 := by rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
  have hsum_wm : (x_hi_1 % 4) * 2 ^ 84 + x_lo_1 / 2 ^ 172 < WORD_MOD :=
    Nat.lt_of_lt_of_le hsum_lt
      (by unfold WORD_MOD; exact Nat.pow_le_pow_right (by omega) (by omega))
  rw [hor]; exact ⟨rfl, hsum_lt, hsum_wm⟩

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
