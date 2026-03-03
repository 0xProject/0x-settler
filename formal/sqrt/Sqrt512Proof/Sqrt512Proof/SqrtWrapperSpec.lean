/-
  Bridge proof: model_sqrt512_wrapper_evm computes natSqrt.

  The auto-generated model_sqrt512_wrapper_evm dispatches:
    x_hi = 0 ⟹ inlined 256-bit floor sqrt (= model_sqrt_floor_evm from SqrtProof)
    x_hi > 0 ⟹ model_sqrt512_evm (already proved correct)
-/
import Sqrt512Proof.GeneratedSqrt512Model
import Sqrt512Proof.GeneratedSqrt512Spec
import SqrtProof.GeneratedSqrtModel
import SqrtProof.GeneratedSqrtSpec
import SqrtProof.SqrtCorrect

namespace Sqrt512Spec

open Sqrt512GeneratedModel

-- ============================================================================
-- Section 1: Namespace compatibility
-- Both SqrtGeneratedModel and Sqrt512GeneratedModel define identical opcodes.
-- We prove extensional equality so we can rewrite the wrapper's x_hi=0 branch
-- from Sqrt512GeneratedModel ops to SqrtGeneratedModel ops.
-- ============================================================================

section NamespaceCompat

theorem WORD_MOD_compat :
    @Sqrt512GeneratedModel.WORD_MOD = @SqrtGeneratedModel.WORD_MOD := rfl

theorem u256_compat (x : Nat) :
    Sqrt512GeneratedModel.u256 x = SqrtGeneratedModel.u256 x := by
  unfold Sqrt512GeneratedModel.u256 SqrtGeneratedModel.u256
  rw [WORD_MOD_compat]

theorem evmAdd_compat (a b : Nat) :
    Sqrt512GeneratedModel.evmAdd a b = SqrtGeneratedModel.evmAdd a b := by
  unfold Sqrt512GeneratedModel.evmAdd SqrtGeneratedModel.evmAdd
  simp [u256_compat]

theorem evmSub_compat (a b : Nat) :
    Sqrt512GeneratedModel.evmSub a b = SqrtGeneratedModel.evmSub a b := by
  unfold Sqrt512GeneratedModel.evmSub SqrtGeneratedModel.evmSub
  simp [u256_compat, WORD_MOD_compat]

theorem evmMul_compat (a b : Nat) :
    Sqrt512GeneratedModel.evmMul a b = SqrtGeneratedModel.evmMul a b := by
  unfold Sqrt512GeneratedModel.evmMul SqrtGeneratedModel.evmMul
  simp [u256_compat]

theorem evmDiv_compat (a b : Nat) :
    Sqrt512GeneratedModel.evmDiv a b = SqrtGeneratedModel.evmDiv a b := by
  unfold Sqrt512GeneratedModel.evmDiv SqrtGeneratedModel.evmDiv
  simp [u256_compat]

theorem evmShl_compat (s v : Nat) :
    Sqrt512GeneratedModel.evmShl s v = SqrtGeneratedModel.evmShl s v := by
  unfold Sqrt512GeneratedModel.evmShl SqrtGeneratedModel.evmShl
  simp [u256_compat]

theorem evmShr_compat (s v : Nat) :
    Sqrt512GeneratedModel.evmShr s v = SqrtGeneratedModel.evmShr s v := by
  unfold Sqrt512GeneratedModel.evmShr SqrtGeneratedModel.evmShr
  simp [u256_compat]

theorem evmClz_compat (v : Nat) :
    Sqrt512GeneratedModel.evmClz v = SqrtGeneratedModel.evmClz v := by
  unfold Sqrt512GeneratedModel.evmClz SqrtGeneratedModel.evmClz
  simp [u256_compat]

theorem evmLt_compat (a b : Nat) :
    Sqrt512GeneratedModel.evmLt a b = SqrtGeneratedModel.evmLt a b := by
  unfold Sqrt512GeneratedModel.evmLt SqrtGeneratedModel.evmLt
  simp [u256_compat]

theorem evmEq_compat (a b : Nat) :
    Sqrt512GeneratedModel.evmEq a b = SqrtGeneratedModel.evmEq a b := by
  unfold Sqrt512GeneratedModel.evmEq SqrtGeneratedModel.evmEq
  simp [u256_compat]

theorem evmGt_compat (a b : Nat) :
    Sqrt512GeneratedModel.evmGt a b = SqrtGeneratedModel.evmGt a b := by
  unfold Sqrt512GeneratedModel.evmGt SqrtGeneratedModel.evmGt
  simp [u256_compat]

theorem evmNot_compat (a : Nat) :
    Sqrt512GeneratedModel.evmNot a = SqrtGeneratedModel.evmNot a := by
  unfold Sqrt512GeneratedModel.evmNot SqrtGeneratedModel.evmNot
  simp [u256_compat, WORD_MOD_compat]

theorem evmMulmod_compat (a b n : Nat) :
    Sqrt512GeneratedModel.evmMulmod a b n = SqrtGeneratedModel.evmMulmod a b n := by
  unfold Sqrt512GeneratedModel.evmMulmod SqrtGeneratedModel.evmMulmod
  simp [u256_compat]

end NamespaceCompat

-- ============================================================================
-- Section 2: The wrapper's x_hi=0 branch equals model_sqrt_floor_evm
-- ============================================================================

/-- u256 is idempotent: u256(u256(x)) = u256(x). -/
private theorem u256_idem (x : Nat) :
    Sqrt512GeneratedModel.u256 (Sqrt512GeneratedModel.u256 x) = Sqrt512GeneratedModel.u256 x := by
  unfold Sqrt512GeneratedModel.u256 Sqrt512GeneratedModel.WORD_MOD
  exact Nat.mod_eq_of_lt (Nat.mod_lt x (Nat.two_pow_pos 256))

theorem su256_idem (x : Nat) :
    SqrtGeneratedModel.u256 (SqrtGeneratedModel.u256 x) = SqrtGeneratedModel.u256 x := by
  unfold SqrtGeneratedModel.u256 SqrtGeneratedModel.WORD_MOD
  exact Nat.mod_eq_of_lt (Nat.mod_lt x (Nat.two_pow_pos 256))

theorem su256_zero : SqrtGeneratedModel.u256 0 = 0 := by
  unfold SqrtGeneratedModel.u256 SqrtGeneratedModel.WORD_MOD; simp

/-- When x_hi = 0, model_sqrt512_wrapper_evm calls model_sqrt256_floor_evm,
    which is identical (modulo namespace) to model_sqrt_floor_evm from SqrtProof. -/
theorem wrapper_zero_eq_sqrt_floor_evm (x_lo : Nat) :
    model_sqrt512_wrapper_evm 0 x_lo = SqrtGeneratedModel.model_sqrt_floor_evm x_lo := by
  -- Unfold all model definitions to expose the full EVM expression
  simp only [model_sqrt512_wrapper_evm, model_sqrt256_floor_evm,
    SqrtGeneratedModel.model_sqrt_floor_evm, SqrtGeneratedModel.model_sqrt_evm]
  -- Convert Sqrt512 namespace ops to SqrtGeneratedModel ops
  simp only [evmEq_compat, evmShr_compat, evmAdd_compat, evmDiv_compat,
    evmSub_compat, evmClz_compat, evmShl_compat, evmLt_compat, u256_compat]
  -- Simplify: u256(u256(x)) = u256(x) and u256(0) = 0
  simp only [su256_zero, su256_idem]
  -- Simplify the conditional: if True then 1 else 0 = 1, 1 ≠ 0 = True, take then-branch
  simp (config := { decide := true })

-- ============================================================================
-- Section 3: natSqrt uniqueness bridge
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
-- Section 4: Main theorem — model_sqrt512_wrapper_evm = natSqrt
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
    rw [SqrtGeneratedModel.model_sqrt_floor_evm_eq_floorSqrt x_lo hxlo]
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
