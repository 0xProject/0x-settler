import ExpProof.Mono.Consts
import Common.Word

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word

/-! Small word facts used by the clamp/pin shell. -/

/-- `evmSlt a b` is the signed comparison of canonical words. -/
theorem evmSlt_eq_ite (a b : Nat) :
    evmSlt a b = if int256 (u256 a) < int256 (u256 b) then 1 else 0 := by
  have hua : u256 a < 2 ^ 256 := u256_lt_word a
  have hub : u256 b < 2 ^ 256 := u256_lt_word b
  have offneg : ∀ c : Nat, c < 2 ^ 256 → 2 ^ 255 ≤ c →
      (c + 2 ^ 255) % 2 ^ 256 = c - 2 ^ 255 := by
    intro c hc hcn
    rw [show c + 2 ^ 255 = (c - 2 ^ 255) + 2 ^ 256 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  have offpos : ∀ c : Nat, c < 2 ^ 256 → c < 2 ^ 255 →
      (c + 2 ^ 255) % 2 ^ 256 = c + 2 ^ 255 := by
    intro c hc hcp
    exact Nat.mod_eq_of_lt (by omega)
  have hai : (u256 a : Int) < 2 ^ 256 := by
    simp only [ipow256]
    exact_mod_cast hua
  have hbi : (u256 b : Int) < 2 ^ 256 := by
    simp only [ipow256]
    exact_mod_cast hub
  have key : ((u256 a + 2 ^ 255) % 2 ^ 256 < (u256 b + 2 ^ 255) % 2 ^ 256) ↔
      (int256 (u256 a) < int256 (u256 b)) := by
    unfold int256
    simp only [ipow256] at hai hbi
    by_cases ha : 2 ^ 255 ≤ u256 a <;> by_cases hb : 2 ^ 255 ≤ u256 b
    · rw [offneg _ hua ha, offneg _ hub hb,
        if_neg (by omega : ¬ u256 a < 2 ^ 255), if_neg (by omega : ¬ u256 b < 2 ^ 255)]
      constructor <;> intro h <;> omega
    · rw [offneg _ hua ha, offpos _ hub (by omega),
        if_neg (by omega : ¬ u256 a < 2 ^ 255), if_pos (by omega : u256 b < 2 ^ 255)]
      constructor <;> intro h <;> omega
    · rw [offpos _ hua (by omega), offneg _ hub hb,
        if_pos (by omega : u256 a < 2 ^ 255), if_neg (by omega : ¬ u256 b < 2 ^ 255)]
      constructor <;> intro h <;> omega
    · rw [offpos _ hua (by omega), offpos _ hub (by omega),
        if_pos (by omega : u256 a < 2 ^ 255), if_pos (by omega : u256 b < 2 ^ 255)]
      constructor <;> intro h <;> omega
  have hslt : evmSlt a b = if int256 (u256 a) < int256 (u256 b) then 1 else 0 := by
    unfold evmSlt
    by_cases hcmp : (u256 a + 2 ^ 255) % WORD_MOD < (u256 b + 2 ^ 255) % WORD_MOD
    · have hcmp' : (u256 a + 2 ^ 255) % 2 ^ 256 < (u256 b + 2 ^ 255) % 2 ^ 256 := hcmp
      rw [if_pos hcmp, if_pos (key.mp hcmp')]
    · have hcmp' : ¬ (u256 a + 2 ^ 255) % 2 ^ 256 < (u256 b + 2 ^ 255) % 2 ^ 256 := hcmp
      rw [if_neg hcmp, if_neg (fun h => hcmp' (key.mpr h))]
  exact hslt

/-- `evmIszero x` is `1` exactly when the canonical word is zero. -/
theorem evmIszero_eq_ite (x : Nat) : evmIszero x = if u256 x = 0 then 1 else 0 := rfl

end ExpYul
