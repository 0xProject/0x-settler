/-
  Bridge proof: model_sqrt512_wrapper_evm computes natSqrt.

  The auto-generated model_sqrt512_wrapper_evm dispatches:
    x_hi = 0 ⟹ inlined 256-bit floor sqrt (= model_sqrt_floor_evm from SqrtProof)
    x_hi > 0 ⟹ model_sqrt512_evm (already proved correct)
-/
import Sqrt512Proof.Sqrt512Yul
import Sqrt512Proof.Sqrt512YulSpec
import SqrtProof.SqrtYul
import SqrtProof.SqrtYulSpec
import SqrtProof.SqrtCorrect

namespace Sqrt512Spec

open Sqrt512Yul
open FormalYul

/-- When x_hi = 0, model_sqrt512_wrapper_evm calls model_sqrt256_floor_evm,
    which is the generated 256-bit floor sqrt model from SqrtProof. -/
theorem wrapper_zero_eq_sqrt_floor_evm (x_lo : Nat) :
    model_sqrt512_wrapper_evm 0 x_lo = SqrtYul.model_sqrt_floor_evm x_lo := by
  simp only [model_sqrt512_wrapper_evm, model_sqrt256_floor_evm,
    SqrtYul.model_sqrt_floor_evm, SqrtYul.model_sqrt_evm]
  simp (config := { decide := true }) [FormalYul.u256, FormalYul.WORD_MOD]

-- ============================================================================
-- natSqrt uniqueness bridge
-- ============================================================================

/-- The integer square root is unique: if r² ≤ n < (r+1)² then r = natSqrt n. -/
theorem natSqrt_unique (n r : Nat) (hlo : r * r ≤ n) (hhi : n < (r + 1) * (r + 1)) :
    r = natSqrt n := by
  have hs := natSqrt_spec n
  -- natSqrt n * natSqrt n ≤ n ∧ n < (natSqrt n + 1) * (natSqrt n + 1)
  suffices h : ¬(r < natSqrt n) ∧ ¬(natSqrt n < r) by omega
  constructor
  · intro hlt
    have hle : r + 1 ≤ natSqrt n := by omega
    have := Nat.mul_le_mul hle hle
    omega
  · intro hlt
    have hle : natSqrt n + 1 ≤ r := by omega
    have := Nat.mul_le_mul hle hle
    omega

/-- floorSqrt = natSqrt for uint256 inputs. -/
theorem floorSqrt_eq_natSqrt (x : Nat) (hx : x < 2 ^ 256) :
    floorSqrt x = natSqrt x := by
  have ⟨hlo, hhi⟩ := floorSqrt_correct_u256 x hx
  exact natSqrt_unique x (floorSqrt x) hlo hhi

-- ============================================================================
-- Main theorem — model_sqrt512_wrapper_evm = natSqrt
-- ============================================================================

set_option exponentiation.threshold 512 in
/-- The EVM model of the sqrt(uint512) wrapper computes natSqrt. -/
theorem model_sqrt512_wrapper_evm_correct (x_hi x_lo : Nat)
    (hxhi : x_hi < 2 ^ 256) (hxlo : x_lo < 2 ^ 256) :
    model_sqrt512_wrapper_evm x_hi x_lo = natSqrt (x_hi * 2 ^ 256 + x_lo) := by
  by_cases hxhi0 : x_hi = 0
  · -- x_hi = 0: the wrapper uses the inlined 256-bit floor sqrt
    subst hxhi0
    simp only [Nat.zero_mul, Nat.zero_add]
    -- Step 1: wrapper's x_hi=0 branch = model_sqrt_floor_evm x_lo
    rw [wrapper_zero_eq_sqrt_floor_evm x_lo]
    -- Step 2: model_sqrt_floor_evm = floorSqrt
    rw [SqrtYul.model_sqrt_floor_evm_eq_floorSqrt x_lo hxlo]
    -- Step 3: floorSqrt = natSqrt
    exact floorSqrt_eq_natSqrt x_lo hxlo
  · -- x_hi > 0: use the existing model_sqrt512_evm_correct
    have hxhi_pos : 0 < x_hi := Nat.pos_of_ne_zero hxhi0
    -- The wrapper's else-branch calls model_sqrt512_evm directly.
    -- After unfolding the wrapper, the else-branch is model_sqrt512_evm (u256 x_hi) (u256 x_lo).
    -- Since x_hi, x_lo < 2^256, u256 is identity.
    unfold model_sqrt512_wrapper_evm
    have hxhi_u : u256 x_hi = x_hi := u256_id' x_hi (by rwa [WORD_MOD])
    have hxlo_u : u256 x_lo = x_lo := u256_id' x_lo (by rwa [WORD_MOD])
    simp only [hxhi_u, hxlo_u]
    -- evmEq x_hi 0 = 0 when x_hi > 0
    have hneq : evmEq x_hi 0 = 0 := by
      unfold evmEq
      simp [u256_id' x_hi (by rwa [WORD_MOD] : x_hi < WORD_MOD)]
      exact Nat.ne_of_gt hxhi_pos
    simp only [hneq]
    -- Now goal is: model_sqrt512_evm x_hi x_lo = natSqrt (x_hi * 2^256 + x_lo)
    exact model_sqrt512_evm_correct x_hi x_lo hxhi_pos hxhi hxlo

end Sqrt512Spec
