import ExpProof.Mono.WordFacts

/-!
# Word-level bridges for signed Exp values and `mulExpRay` guards

Signed-width cleanup applies to both public Exp results. Comparison and boolean-word facts connect
the `mulExpRay` guard operations to their arithmetic predicates. These facts extend
`Mono.WordFacts`.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word

set_option maxRecDepth 100000

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

private theorem word_and (a b : Nat) :
    word a &&& word b = word (evmAnd a b) := by
  simpa only [word] using
    FormalYul.Preservation.uint256_ofNat_and_eq_word_evmAnd a b

private theorem word_or (a b : Nat) :
    word a ||| word b = word (evmOr a b) := by
  simpa only [word] using
    FormalYul.Preservation.uint256_ofNat_or_eq_word_evmOr a b

private theorem signextend_15_eq_ite (w : Nat) :
    EvmYul.UInt256.signextend (word 15) (word w) =
      if word w &&& word (2 ^ 127) ≠ word 0 then
        word w ||| word (2 ^ 256 - 2 ^ 127)
      else
        word w &&& word (2 ^ 127 - 1) := by
  unfold EvmYul.UInt256.signextend
  rw [if_pos (by decide)]
  change
    (if word w &&& word (2 ^ 127) ≠ word 0 then
      word w ||| word (2 ^ 256 - 2 ^ 127)
    else
      word w &&& word (2 ^ 127 - 1)) = _
  rfl

private theorem and_pow127_eq_zero_of_lt {n : Nat} (hn : n < 2 ^ 127) :
    n &&& 2 ^ 127 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hi : i = 127
  · subst i
    simp [Nat.testBit_lt_two_pow hn]
  · simp [Ne.symm hi]

private theorem testBit_pow256_sub_pos_le_pow127 {n : Nat} (hnpos : 0 < n)
    (hn : n ≤ 2 ^ 127) :
    (2 ^ 256 - n).testBit 127 = true := by
  have hnrepr : n = (n - 1) + 1 := by omega
  rw [hnrepr, Nat.testBit_two_pow_sub_succ (by omega : n - 1 < 2 ^ 256)]
  simp [Nat.testBit_lt_two_pow (by omega : n - 1 < 2 ^ 127)]

private theorem and_pow127_eq_pow127_of_testBit {n : Nat}
    (hbit : n.testBit 127 = true) :
    n &&& 2 ^ 127 = 2 ^ 127 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hi : i = 127
  · subst i
    simp [hbit]
  · simp [Ne.symm hi]

private theorem or_sign_mask_eq_self {n : Nat} (hnpos : 0 < n) (hn : n ≤ 2 ^ 127) :
    (2 ^ 256 - n) ||| (2 ^ 256 - 2 ^ 127) = 2 ^ 256 - n := by
  let low := 2 ^ 127 - n
  let high := 2 ^ 129 - 1
  have hlowDef : low = 2 ^ 127 - n := rfl
  have hhighDef : high = 2 ^ 129 - 1 := rfl
  have hlow : low < 2 ^ 127 := by
    rw [hlowDef]
    omega
  have hmask : 2 ^ 256 - 2 ^ 127 = 2 ^ 127 * high := by
    rw [hhighDef]
    calc
      2 ^ 256 - 2 ^ 127 = 2 ^ 127 * 2 ^ 129 - 2 ^ 127 := by
        rw [show 256 = 127 + 129 by omega, Nat.pow_add]
      _ = 2 ^ 127 * (2 ^ 129 - 1) := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  have hword : 2 ^ 256 - n = 2 ^ 127 * high + low := by
    rw [← hmask]
    rw [hlowDef]
    omega
  have hconcat : 2 ^ 127 * high + low = 2 ^ 127 * high ||| low :=
    Nat.two_pow_add_eq_or_of_lt hlow high
  calc
    (2 ^ 256 - n) ||| (2 ^ 256 - 2 ^ 127) =
        (2 ^ 127 * high ||| low) ||| 2 ^ 127 * high := by rw [hword, hmask, hconcat]
    _ = 2 ^ 127 * high ||| low := by
      rw [Nat.or_assoc, Nat.or_comm low (2 ^ 127 * high), ← Nat.or_assoc, Nat.or_self]
    _ = 2 ^ 256 - n := by rw [← hconcat, ← hword]

theorem signextend_15_nonnegative {n : Nat} (hn : n < 2 ^ 127) :
    EvmYul.UInt256.signextend (word 15) (word n) = word n := by
  have hlandZero : word n &&& word (2 ^ 127) = word 0 := by
    rw [word_and, FormalYul.Preservation.evmAnd_eq_of_lt]
    · rw [and_pow127_eq_zero_of_lt hn]
    · simpa [WORD_MOD] using lt_trans hn (by norm_num : 2 ^ 127 < 2 ^ 256)
    · norm_num [WORD_MOD]
  have hlandSelf : word n &&& word (2 ^ 127 - 1) = word n := by
    rw [word_and, FormalYul.Preservation.evmAnd_eq_of_lt]
    · rw [Nat.and_two_pow_sub_one_of_lt_two_pow hn]
    · simpa [WORD_MOD] using lt_trans hn (by norm_num : 2 ^ 127 < 2 ^ 256)
    · norm_num [WORD_MOD]
  rw [signextend_15_eq_ite, hlandZero, if_neg (by simp), hlandSelf]

theorem signextend_15_negative {n : Nat} (hnpos : 0 < n) (hn : n ≤ 2 ^ 127) :
    EvmYul.UInt256.signextend (word 15) (word (2 ^ 256 - n)) = word (2 ^ 256 - n) := by
  have hlandSign :
      word (2 ^ 256 - n) &&& word (2 ^ 127) = word (2 ^ 127) := by
    rw [word_and, FormalYul.Preservation.evmAnd_eq_of_lt]
    · rw [and_pow127_eq_pow127_of_testBit (testBit_pow256_sub_pos_le_pow127 hnpos hn)]
    · norm_num [WORD_MOD]
      omega
    · norm_num [WORD_MOD]
  have hlorSelf :
      word (2 ^ 256 - n) ||| word (2 ^ 256 - 2 ^ 127) =
        word (2 ^ 256 - n) := by
    rw [word_or, FormalYul.Preservation.evmOr_eq_of_lt]
    · rw [or_sign_mask_eq_self hnpos hn]
    · norm_num [WORD_MOD]
      omega
    · norm_num [WORD_MOD]
  rw [signextend_15_eq_ite, hlandSign, if_pos (by decide), hlorSelf]

theorem signextend_15_canonical {w : Nat}
    (hw : w < 2 ^ 127 ∨ ∃ n, 0 < n ∧ n ≤ 2 ^ 127 ∧ w = 2 ^ 256 - n) :
    EvmYul.UInt256.signextend (word 15) (word w) = word w := by
  rcases hw with hw | ⟨n, hnpos, hn, rfl⟩
  · exact signextend_15_nonnegative hw
  · exact signextend_15_negative hnpos hn

theorem signextend_15_eq_self_of_int256_range {w : Nat} (hw : w < 2 ^ 256)
    (hlo : -(2 ^ 127 : Int) ≤ int256 w) (hhi : int256 w < 2 ^ 127) :
    EvmYul.UInt256.signextend (word 15) (word w) = word w := by
  apply signextend_15_canonical
  by_cases hpos : w < 2 ^ 255
  · left
    have hwi : int256 w = (w : Int) := int256_of_lt hpos
    have h : ((w : Nat) : Int) < 2 ^ 127 := by rw [← hwi]; exact hhi
    exact_mod_cast h
  · right
    have hwloInt : (2 ^ 256 : Int) - 2 ^ 127 ≤ (w : Int) := by
      unfold int256 at hlo
      rw [if_neg hpos] at hlo
      omega
    have hbaseCast : ((2 ^ 256 - 2 ^ 127 : Nat) : Int) =
        (2 ^ 256 : Int) - 2 ^ 127 := by norm_num
    have hwlo : 2 ^ 256 - 2 ^ 127 ≤ w := by
      rw [← hbaseCast] at hwloInt
      exact_mod_cast hwloInt
    refine ⟨2 ^ 256 - w, by omega, by omega, by omega⟩

end ExpYul
