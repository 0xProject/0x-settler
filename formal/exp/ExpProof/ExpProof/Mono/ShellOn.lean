import ExpProof.Mono.Tree

/-!
# The masked-on region: `int256 (expTree x) = [x = 0] + int256 (r1Tree x)`

Above the clamp boundary the clamp word is `1`, so the body value passes through and only the
`x = 0` pin adds one. The decode is proved for an *abstract* body word `R` (never the deep tree),
then specialised, so the kernel never has to reduce the Horner accumulator.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word

set_option maxRecDepth 100000

private theorem evmMul_one_left' {b : Nat} (hb : b < 2 ^ 256) : evmMul 1 b = b := by
  have h1 : u256 1 = 1 := by unfold u256; simp [word_mod_eq]
  have hbb : u256 b = b := u256_of_lt hb
  unfold evmMul; rw [h1, hbb, Nat.one_mul, hbb]
private theorem evmAdd_zero_left' {b : Nat} (hb : b < 2 ^ 256) : evmAdd 0 b = b := by
  have h0 : u256 0 = 0 := by unfold u256; simp
  have hbb : u256 b = b := u256_of_lt hb
  unfold evmAdd; rw [h0, hbb, Nat.zero_add, hbb]

/-- The clamp/pin shell decode for an abstract body word `R` above the boundary. -/
theorem int256_shell_of_gt {x R : Nat}
    (hmask : int256 (u256 Cmask) < int256 (u256 x)) (hR : R < 2 ^ 254) :
    int256 (evmAdd (evmIszero x) (evmMul (evmSlt Cmask x) R)) =
      (if u256 x = 0 then 1 else 0) + (R : Int) := by
  have hR' : R < 2 ^ 255 := by have : (2:Nat)^254 < 2^255 := by norm_num
                               omega
  have hRlt : R < 2 ^ 256 := by have : (2:Nat)^254 < 2^256 := by norm_num
                                omega
  have hsl : evmSlt Cmask x = 1 := by rw [evmSlt_eq_ite, if_pos hmask]
  rw [hsl, evmMul_one_left' hRlt]
  unfold evmIszero
  have h1 : int256 1 = 1 := by decide
  have hRnn : int256 R = (R : Int) := int256_of_lt hR'
  have hpow : (2 : Int) ^ 254 < 2 ^ 255 := by norm_num
  by_cases hx0 : u256 x = 0
  · rw [if_pos hx0, evmAdd_int256 (by norm_num) hRlt
      (by rw [h1, hRnn]; simp only [ipow255]; omega)
      (by rw [h1, hRnn]; simp only [ipow255] at hpow ⊢; omega), if_pos hx0, h1, hRnn]
  · rw [if_neg hx0, evmAdd_zero_left' hRlt, if_neg hx0, int256_of_lt hR']; ring

/-- Specialisation to the actual body word `r1Tree x`. -/
theorem int256_expTree_of_gt {x : Nat}
    (hmask : int256 (u256 Cmask) < int256 (u256 x))
    (hr1 : r1Tree x < 2 ^ 254) :
    int256 (expTree x) = (if u256 x = 0 then 1 else 0) + (r1Tree x : Int) :=
  int256_shell_of_gt hmask hr1

end ExpYul
