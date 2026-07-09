import ExpProof.Mono.WordFacts

/-!
# Word-level bridges for the `mulExpRay` guard

Comparison and boolean-word facts that translate the compiled guard word into signed
predicates. They complement `Mono.WordFacts` without disturbing its downstream consumers.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word

/-- `evmSgt` is `evmSlt` with the operands swapped. -/
theorem evmSgt_eq_evmSlt_swap (a b : Nat) : evmSgt a b = evmSlt b a := rfl

/-- `evmGt a b` compares the canonical words unsigned. -/
theorem evmGt_eq_ite (a b : Nat) : evmGt a b = if u256 b < u256 a then 1 else 0 := rfl

/-- `evmEq a b` compares the canonical words. -/
theorem evmEq_eq_ite (a b : Nat) : evmEq a b = if u256 a = u256 b then 1 else 0 := rfl

/-- A canonical word is signed-zero exactly when it is the zero word. -/
theorem int256_zero_iff_of_canonical {x : Nat} (hx : x < 2 ^ 256) : int256 x = 0 ↔ x = 0 := by
  unfold int256
  have hx' : (x : Int) < 2 ^ 256 := by exact_mod_cast hx
  split_ifs <;> omega

/-- An `if`-encoded boolean word is zero exactly when its condition fails. -/
theorem ite_one_zero_eq_zero_iff {c : Prop} [Decidable c] :
    (if c then (1 : Nat) else 0) = 0 ↔ ¬c := by
  split_ifs with h <;> simp [h]

/-- An `if`-encoded boolean word is one exactly when its condition holds. -/
theorem ite_one_zero_eq_one_iff {c : Prop} [Decidable c] :
    (if c then (1 : Nat) else 0) = 1 ↔ c := by
  split_ifs with h <;> simp [h]

/-- `evmIszero` negates an `if`-encoded boolean word. -/
theorem evmIszero_ite (c : Prop) [Decidable c] :
    evmIszero (if c then (1 : Nat) else 0) = if c then 0 else 1 := by
  unfold evmIszero u256 WORD_MOD
  split_ifs <;> simp_all

/-- `evmOr` of `if`-encoded boolean words is the disjunction. -/
theorem evmOr_ite (c d : Prop) [Decidable c] [Decidable d] :
    evmOr (if c then (1 : Nat) else 0) (if d then (1 : Nat) else 0) =
      if c ∨ d then 1 else 0 := by
  unfold evmOr u256 WORD_MOD
  split_ifs <;> simp_all

/-- `evmAnd` of `if`-encoded boolean words is the conjunction. -/
theorem evmAnd_ite (c d : Prop) [Decidable c] [Decidable d] :
    evmAnd (if c then (1 : Nat) else 0) (if d then (1 : Nat) else 0) =
      if c ∧ d then 1 else 0 := by
  unfold evmAnd u256 WORD_MOD
  split_ifs <;> simp_all

end ExpYul
