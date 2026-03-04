/-
  Base case: model_cbrtBaseCase_evm(x_hi_1) returns (r_hi, res, d) where
    r_hi = icbrt(x_hi_1 / 4)
    res = x_hi_1 / 4 - r_hi³
    d = 3 * r_hi²

  For x_hi_1 ∈ [2^253, 2^256):
    x_hi_1 / 4 ∈ [2^251, 2^254)  (octaves 251-253)
    r_hi = icbrt(x_hi_1/4) ∈ [2^83, 2^85)
-/
import Cbrt512Proof.GeneratedCbrt512Model
import CbrtProof.CbrtCorrect
import CbrtProof.CertifiedChain
import CbrtProof.FiniteCert
import CbrtProof.Wiring

namespace Cbrt512Spec

open Cbrt512GeneratedModel
open CbrtCertified
open CbrtCert

-- ============================================================================
-- NR step EVM bridge
-- ============================================================================

/-- model_cbrtNRStep_evm(x, r) = cbrtStep(x, r) when intermediate values fit in uint256. -/
theorem model_cbrtNRStep_evm_eq_cbrtStep (x r : Nat)
    (hx : x < WORD_MOD) (hr : r < WORD_MOD)
    (hrr : r * r < WORD_MOD)
    (hsum : x / (r * r) + 2 * r < WORD_MOD) :
    model_cbrtNRStep_evm x r = cbrtStep x r := by
  unfold model_cbrtNRStep_evm cbrtStep
  simp only [u256, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hr]
  have hmul_rr : evmMul r r = r * r := by
    unfold evmMul u256; simp [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hrr]
  have hdiv_xrr : evmDiv x (evmMul r r) = x / (r * r) := by
    rw [hmul_rr]; unfold evmDiv u256
    rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hrr]
    by_cases hrr0 : r * r = 0
    · simp [hrr0]
    · simp [hrr0, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self x _) hx)]
  have hdiv_lt : x / (r * r) < WORD_MOD :=
    Nat.lt_of_le_of_lt (Nat.div_le_self x _) hx
  have hadd1_lt : x / (r * r) + r < WORD_MOD := by omega
  have hadd1 : evmAdd (evmDiv x (evmMul r r)) r = x / (r * r) + r := by
    rw [hdiv_xrr]; unfold evmAdd u256
    simp [Nat.mod_eq_of_lt hdiv_lt, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hadd1_lt]
  have hadd2 : evmAdd (evmAdd (evmDiv x (evmMul r r)) r) r = x / (r * r) + 2 * r := by
    rw [hadd1]; unfold evmAdd u256
    rw [Nat.mod_eq_of_lt hadd1_lt, Nat.mod_eq_of_lt hr]
    rw [show x / (r * r) + r + r = x / (r * r) + 2 * r from by omega]
    exact Nat.mod_eq_of_lt hsum
  have h3_wm : (3 : Nat) < WORD_MOD := by unfold WORD_MOD; omega
  rw [hadd2]; unfold evmDiv u256
  simp [Nat.mod_eq_of_lt hsum, Nat.mod_eq_of_lt h3_wm]

-- ============================================================================
-- Base case NR convergence
-- ============================================================================

/-- The 6 NR steps from the fixed seed converge to within ±1 of icbrt(w)
    for w ∈ [2^251, 2^254). -/
theorem baseCase_NR_within_1ulp (w : Nat)
    (hw_lo : 2 ^ 251 ≤ w) (hw_hi : w < 2 ^ 254) :
    let m := icbrt w
    let z := run6From w 22141993662453218394297550
    m ≤ z ∧ z ≤ m + 1 := by
  -- Proof uses per-octave certificates for the fixed seed.
  -- Each octave gives: run6From w seed ≤ m + 1 via chaining step_from_bound.
  -- Lower bound: cbrt_step_floor_bound at each step.
  sorry

/-- On a perfect cube w = m³ with m ≥ 2^83, the 6 NR steps give exactly m. -/
theorem baseCase_NR_exact_on_perfect_cube (m : Nat)
    (hm_lo : 2 ^ 83 ≤ m) (hm_hi : m < 2 ^ 85)
    (hw_range : m * m * m < 2 ^ 254) :
    run6From (m * m * m) 22141993662453218394297550 = m := by
  sorry

-- ============================================================================
-- Base case EVM bridge
-- ============================================================================

/-- The base case EVM model matches the 256-bit cbrt for the normalized input. -/
theorem model_cbrtBaseCase_evm_correct (x_hi_1 : Nat)
    (hx_lo : 2 ^ 253 ≤ x_hi_1) (hx_hi : x_hi_1 < WORD_MOD) :
    let w := x_hi_1 / 4
    let m := icbrt w
    let bc := model_cbrtBaseCase_evm x_hi_1
    bc.1 = m ∧
    bc.2.1 = w - m * m * m ∧
    bc.2.2 = 3 * (m * m) ∧
    2 ^ 83 ≤ m ∧ m < 2 ^ 85 ∧
    m * m * m ≤ w ∧
    w - m * m * m ≤ 3 * (m * m) + 3 * m ∧
    m < WORD_MOD ∧
    m * m < WORD_MOD ∧
    3 * (m * m) < WORD_MOD ∧
    3 * (m * m) > 0 := by
  sorry

end Cbrt512Spec
