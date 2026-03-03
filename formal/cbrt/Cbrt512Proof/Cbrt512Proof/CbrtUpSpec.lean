/-
  Bridge proof: model_cbrtUp512_wrapper_evm computes cbrtUp512.

  The auto-generated model_cbrtUp512_wrapper_evm dispatches:
    x_hi = 0 ⟹ inlined 256-bit ceiling cbrt (= model_cbrt_up_evm from CbrtProof)
    x_hi > 0 ⟹ model_cbrt512_evm (within 1ulp) + cube-and-compare + increment
-/
import Cbrt512Proof.GeneratedCbrt512Model
import Cbrt512Proof.GeneratedCbrt512Spec
import Cbrt512Proof.Cbrt512Correct
import Cbrt512Proof.CbrtWrapperSpec
import CbrtProof.GeneratedCbrtModel
import CbrtProof.GeneratedCbrtSpec
import CbrtProof.CbrtCorrect

namespace Cbrt512Spec

open Cbrt512GeneratedModel

-- ============================================================================
-- Section 1: x_hi = 0 branch — bridge to model_cbrt_up_evm
-- ============================================================================

/-- When x_hi = 0, model_cbrtUp512_wrapper_evm equals model_cbrt_up_evm from CbrtProof. -/
theorem cbrtUp_wrapper_zero_eq_cbrt_up_evm (x_lo : Nat) :
    model_cbrtUp512_wrapper_evm 0 x_lo = CbrtGeneratedModel.model_cbrt_up_evm x_lo := by
  simp only [model_cbrtUp512_wrapper_evm, model_cbrt256_up_evm,
    CbrtGeneratedModel.model_cbrt_up_evm, CbrtGeneratedModel.model_cbrt_evm]
  simp only [evmEq_compat, evmShr_compat, evmAdd_compat, evmDiv_compat,
    evmSub_compat, evmClz_compat, evmShl_compat, evmLt_compat,
    evmMul_compat, evmGt_compat, u256_compat]
  simp only [cu256_zero, cu256_idem]
  simp (config := { decide := true })

-- ============================================================================
-- Section 2: Ceiling cbrt uniqueness
-- ============================================================================

/-- Ceiling cube root uniqueness: if x ≤ r³ and r is minimal, then r = cbrtUp512 x. -/
theorem cbrtUp512_unique (x r : Nat) (hx : x < 2 ^ 512)
    (hle : x ≤ r * r * r) (hmin : ∀ y, x ≤ y * y * y → r ≤ y) :
    r = cbrtUp512 x := by
  have ⟨hup_le, hup_min⟩ := cbrtUp512_correct x hx
  have h1 := hmin (cbrtUp512 x) hup_le
  have h2 := hup_min r hle
  omega

-- ============================================================================
-- Section 3: Main theorem — model_cbrtUp512_wrapper_evm = cbrtUp512
-- ============================================================================

set_option exponentiation.threshold 1024 in
/-- The EVM model of cbrtUp(uint512) computes cbrtUp512. -/
theorem model_cbrtUp512_wrapper_evm_correct (x_hi x_lo : Nat)
    (hxhi : x_hi < 2 ^ 256) (hxlo : x_lo < 2 ^ 256) :
    model_cbrtUp512_wrapper_evm x_hi x_lo = cbrtUp512 (x_hi * 2 ^ 256 + x_lo) := by
  by_cases hxhi0 : x_hi = 0
  · -- x_hi = 0: use 256-bit ceiling cbrt bridge
    subst hxhi0
    simp only [Nat.zero_mul, Nat.zero_add]
    rw [cbrtUp_wrapper_zero_eq_cbrt_up_evm]
    -- model_cbrt_up_evm x_lo satisfies ceiling cbrt spec
    have hspec := CbrtGeneratedModel.model_cbrt_up_evm_ceil_u256 x_lo hxlo
    -- Both satisfy the same uniqueness property
    have hx512 : x_lo < 2 ^ 512 := by
      calc x_lo < 2 ^ 256 := hxlo
        _ ≤ 2 ^ 512 := Nat.pow_le_pow_right (by omega) (by omega)
    exact cbrtUp512_unique x_lo (CbrtGeneratedModel.model_cbrt_up_evm x_lo) hx512
      hspec.1 hspec.2
  · -- x_hi > 0: floor cbrt + comparison + increment
    sorry

end Cbrt512Spec
