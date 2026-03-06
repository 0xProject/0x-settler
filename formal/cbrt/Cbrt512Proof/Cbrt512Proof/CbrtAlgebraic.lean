/-
  Shared algebraic lemmas for the 512-bit cbrt composition proof.
  Used by CbrtComposition.lean for sub-lemmas A and B.
-/
import Cbrt512Proof.GeneratedCbrt512Model
import Cbrt512Proof.EvmBridge
import Cbrt512Proof.CbrtBaseCase
import Cbrt512Proof.CbrtKaratsubaQuotient
import CbrtProof.CbrtCorrect

set_option exponentiation.threshold 1024

namespace Cbrt512Spec

open Cbrt512GeneratedModel

-- ============================================================================
-- Cube expansion: (a + b)³ = a³ + 3a²b + 3ab² + b³
-- ============================================================================

theorem cube_sum_expand (a b : Nat) :
    (a + b) * (a + b) * (a + b) =
      a * a * a + 3 * (a * a) * b + 3 * a * (b * b) + b * b * b := by
  suffices h : (↑((a + b) * (a + b) * (a + b)) : Int) =
      ↑(a * a * a + 3 * (a * a) * b + 3 * a * (b * b) + b * b * b) by exact_mod_cast h
  push_cast
  simp only [show (3 : Int) = 1 + 1 + 1 from rfl,
             Int.add_mul, Int.mul_add, Int.one_mul]
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  omega

-- ============================================================================
-- R³ factoring: (m * 2^86)³ = m³ * 2^258
-- ============================================================================

theorem R_cube_factor (m : Nat) :
    m * 2 ^ 86 * (m * 2 ^ 86) * (m * 2 ^ 86) = m * m * m * 2 ^ 258 := by
  have h258 : (2 : Nat) ^ 258 = 2 ^ 86 * (2 ^ 86 * 2 ^ 86) := by
    rw [show (258 : Nat) = 86 + (86 + 86) from rfl, Nat.pow_add, Nat.pow_add]
  rw [h258]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

-- ============================================================================
-- d * 2^172 = 3R²: connecting the divisor to the square of R
-- ============================================================================

theorem d_pow172_eq_3R_sq (m : Nat) :
    3 * (m * m) * 2 ^ 172 = 3 * (m * 2 ^ 86 * (m * 2 ^ 86)) := by
  have h172 : (2 : Nat) ^ 172 = 2 ^ 86 * 2 ^ 86 := by
    rw [show (172 : Nat) = 86 + 86 from rfl, Nat.pow_add]
  rw [h172]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

-- ============================================================================
-- x_norm decomposition
-- ============================================================================

/-- The 512-bit input decomposes as m³·2^258 + n_full·2^172 + c_tail. -/
theorem x_norm_decomp (x_hi_1 x_lo_1 m3 : Nat)
    (hm3_le : m3 ≤ x_hi_1 / 4) :
    x_hi_1 * 2 ^ 256 + x_lo_1 =
      m3 * 2 ^ 258 +
      ((x_hi_1 / 4 - m3) * 2 ^ 86 + (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) * 2 ^ 172 +
      x_lo_1 % 2 ^ 172 := by
  have h_xhi := Nat.div_add_mod x_hi_1 4
  have h_xlo := Nat.div_add_mod x_lo_1 (2 ^ 172)
  have h258 : (2 : Nat) ^ 258 = 2 ^ 86 * 2 ^ 172 := by
    rw [show (258 : Nat) = 86 + 172 from rfl, Nat.pow_add]
  have h256 : (2 : Nat) ^ 256 = 2 ^ 84 * 2 ^ 172 := by
    rw [show (256 : Nat) = 84 + 172 from rfl, Nat.pow_add]
  have hn_expand :
      ((x_hi_1 / 4 - m3) * 2 ^ 86 + (x_hi_1 % 4 * 2 ^ 84 + x_lo_1 / 2 ^ 172)) * 2 ^ 172 =
      (x_hi_1 / 4 - m3) * (2 ^ 86 * 2 ^ 172) +
      (x_hi_1 % 4 * 2 ^ 84 * 2 ^ 172 + x_lo_1 / 2 ^ 172 * 2 ^ 172) := by
    rw [Nat.add_mul, Nat.mul_assoc, Nat.add_mul, Nat.mul_assoc]
  rw [hn_expand]
  simp only [Nat.mul_assoc]
  rw [← h258, ← h256]
  omega

-- ============================================================================
-- Square expansion: (a + b)² = a² + 2ab + b²
-- ============================================================================

theorem sq_sum_expand (a b : Nat) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  suffices h : (↑((a + b) * (a + b)) : Int) =
      ↑(a * a + 2 * a * b + b * b) by exact_mod_cast h
  push_cast
  simp only [show (2 : Int) = 1 + 1 from rfl,
             Int.add_mul, Int.mul_add, Int.one_mul]
  simp only [Int.mul_comm]
  omega

end Cbrt512Spec
