import ExpProof.Mono.Tree

/-!
# The clamp/pin shell: reducing `expTree` monotonicity to the meaningful region

`expTree x = evmAdd (evmIszero x) (evmMul (evmSlt C x) (r1Tree x))`. Two regions:

* **masked off** (`int256 (u256 x) ≤ int256 C`): the clamp is `0`, and since `int256 C < 0` the
  pin cannot fire either, so `expTree x = 0`;
* **masked on** (`int256 C < int256 (u256 x)`): the clamp is transparent, so
  `int256 (expTree x) = [x = 0] + int256 (r1Tree x)`.

Given the analytic facts on the masked-on region — `r1Tree` nonnegative and nondecreasing in the
signed input, and the `x = 0` neighbours bracketing the pin — `expTree` is monotone over the whole
domain. This file packages that reduction; the analytic facts are its hypotheses.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word

set_option maxRecDepth 100000

attribute [local irreducible] r1Tree r0Tree evTree odTree todTree tTree vTree kTree

/-- `int256 C < 0`: the clamp boundary is a negative signed value. -/
theorem int256_Cmask_neg : int256 (u256 Cmask) < 0 := by
  rw [u256_of_lt Cmask_lt, int256_Cmask]; norm_num

/-! ## `{0,1}` word arithmetic -/

theorem evmMul_zero_left (b : Nat) : evmMul 0 b = 0 := by
  have h0 : u256 0 = 0 := by unfold u256; simp
  unfold evmMul; rw [h0, Nat.zero_mul]; unfold u256; simp
theorem evmMul_one_left {b : Nat} (hb : b < 2 ^ 256) : evmMul 1 b = b := by
  have h1 : u256 1 = 1 := by unfold u256; simp [word_mod_eq]
  have hbb : u256 b = b := u256_of_lt hb
  unfold evmMul; rw [h1, hbb, Nat.one_mul, hbb]
theorem evmAdd_zero_left {b : Nat} (hb : b < 2 ^ 256) : evmAdd 0 b = b := by
  have h0 : u256 0 = 0 := by unfold u256; simp
  have hbb : u256 b = b := u256_of_lt hb
  unfold evmAdd; rw [h0, hbb, Nat.zero_add, hbb]

/-! ## The masked-off region: `expTree x = 0` -/

/-- Below or at the clamp boundary the result is `0` (the clamp zeroes it and the pin cannot fire
because the boundary is negative, so `x ≠ 0`). -/
theorem expTree_eq_zero_of_le {x : Nat} (h : int256 (u256 x) ≤ int256 (u256 Cmask)) :
    expTree x = 0 := by
  unfold expTree
  have hmask : evmSlt Cmask x = 0 := by
    rw [evmSlt_eq_ite]
    rw [if_neg (by omega : ¬ int256 (u256 Cmask) < int256 (u256 x))]
  have hpin : evmIszero x = 0 := by
    have hxne : u256 x ≠ 0 := by
      intro h0
      have : int256 (u256 x) = 0 := by rw [h0]; rfl
      have hneg := int256_Cmask_neg
      omega
    unfold evmIszero
    rw [if_neg hxne]
  rw [hmask, hpin, evmMul_zero_left]
  rfl

end ExpYul
