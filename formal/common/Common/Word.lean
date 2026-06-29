import FormalYul.Preservation

/-!
# Reusable, contract-agnostic EVM-word lemmas

Function-agnostic facts about the compiled-runtime word operations: the
`u256`/`int256` bounds, the `wordNat`-preservation bridges for `sar`/`sdiv`/`slt`
(which `FormalYul.Preservation` does not provide for signed shifts/division),
and the `u256`-idempotence absorbers for the `evm*` results. They are used by
the runtime reductions of the per-function proofs and contain nothing specific
to any one implementation.
-/

namespace Common.Word

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

theorem word_mod_eq : WORD_MOD = 2 ^ 256 := rfl

theorem u256_lt_word (x : Nat) : u256 x < 2 ^ 256 := by
  unfold u256 WORD_MOD
  exact Nat.mod_lt _ (Nat.two_pow_pos 256)

theorem u256_idem (x : Nat) : u256 (u256 x) = u256 x := by
  unfold u256 WORD_MOD
  exact Nat.mod_mod_of_dvd x (dvd_refl _)

theorem u256_pos_bounds {x : Nat} (h : 0 < int256 (u256 x)) :
    1 ≤ u256 x ∧ u256 x < 2 ^ 255 := by
  have hlt : u256 x < 2 ^ 256 := u256_lt_word x
  unfold int256 at h
  by_cases hb : u256 x < 2 ^ 255
  · simp only [hb, if_true] at h
    have : 0 < u256 x := by exact_mod_cast h
    exact ⟨this, hb⟩
  · exfalso
    simp only [hb, if_false] at h
    rw [intPow256] at h
    have : (u256 x : Int) < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      rw [← intPow256]; exact_mod_cast hlt
    omega

theorem wordNat_complement (a : EvmYul.UInt256) :
    wordNat (EvmYul.UInt256.complement a) = evmNot (wordNat a) := by
  have hav : a.toNat < 2 ^ 256 := by
    simp [EvmYul.UInt256.toNat, EvmYul.UInt256.size]
  simp only [wordNat, EvmYul.UInt256.complement, EvmYul.UInt256.toNat, evmNot, u256, WORD_MOD,
    Fin.sub_def, Fin.add_def, Fin.val_zero, Fin.val_one, EvmYul.UInt256.size]
  omega

theorem wordNat_sar (a b : EvmYul.UInt256) :
    wordNat (EvmYul.UInt256.sar a b) = evmSar (wordNat a) (wordNat b) := by
  have hb : wordNat b < 2 ^ 256 := by
    simp [EvmYul.UInt256.toNat, EvmYul.UInt256.size, wordNat]
  have ha : wordNat a < 2 ^ 256 := by
    simp [EvmYul.UInt256.toNat, EvmYul.UInt256.size, wordNat]
  have huina : u256 (wordNat a) = wordNat a := by
    unfold u256 WORD_MOD; exact Nat.mod_eq_of_lt ha
  have huinb : u256 (wordNat b) = wordNat b := by
    unfold u256 WORD_MOD; exact Nat.mod_eq_of_lt hb
  have hbz : ¬ (b < (⟨0⟩ : EvmYul.UInt256)) := by
    have hz : (⟨0⟩ : EvmYul.UInt256).toNat = 0 := rfl
    show ¬ (b.toNat < (⟨0⟩ : EvmYul.UInt256).toNat)
    rw [hz]; omega
  have hsltz : EvmYul.UInt256.sltBool b ⟨0⟩ = true ↔ 2 ^ 255 ≤ wordNat b := by
    unfold EvmYul.UInt256.sltBool
    by_cases hb255 : 2 ^ 255 ≤ wordNat b <;>
      simp [hbz, wordNat, show (⟨0⟩ : EvmYul.UInt256).toNat = 0 from rfl]
  unfold EvmYul.UInt256.sar
  by_cases hneg : EvmYul.UInt256.sltBool b ⟨0⟩ = true
  · rw [if_pos hneg]
    have hvneg : 2 ^ 255 ≤ wordNat b := hsltz.mp hneg
    rw [show (EvmYul.UInt256.complement b) >>> a
          = EvmYul.UInt256.shiftRight (EvmYul.UInt256.complement b) a from rfl,
        wordNat_complement, wordNat_shiftRight, wordNat_complement]
    simp only [evmSar, evmShr, evmNot]
    rw [huina, huinb, if_pos hvneg]
    have hnotv : u256 (WORD_MOD - 1 - wordNat b) = WORD_MOD - 1 - wordNat b := by
      unfold u256 WORD_MOD; apply Nat.mod_eq_of_lt; unfold WORD_MOD at hb; omega
    rw [hnotv]
    by_cases hs : wordNat a < 256
    · rw [if_pos hs, if_neg (by omega : ¬ 256 ≤ wordNat a)]
      have hdiv : u256 ((WORD_MOD - 1 - wordNat b) / 2 ^ wordNat a)
          = (WORD_MOD - 1 - wordNat b) / 2 ^ wordNat a := by
        unfold u256 WORD_MOD; apply Nat.mod_eq_of_lt
        have hle : (2 ^ 256 - 1 - wordNat b) / 2 ^ wordNat a ≤ 2 ^ 256 - 1 - wordNat b :=
          Nat.div_le_self _ _
        unfold WORD_MOD at hb; omega
      rw [hdiv]
    · rw [if_neg hs, if_pos (by omega : 256 ≤ wordNat a)]
      have : u256 0 = 0 := by unfold u256 WORD_MOD; simp
      rw [this]; omega
  · rw [if_neg hneg]
    have hvpos : wordNat b < 2 ^ 255 := by
      by_contra hc; push_neg at hc; exact hneg (hsltz.mpr hc)
    rw [show b >>> a = EvmYul.UInt256.shiftRight b a from rfl, wordNat_shiftRight]
    simp only [evmSar, evmShr]
    rw [huina, huinb, if_neg (by omega : ¬ 2 ^ 255 ≤ wordNat b)]
    split_ifs <;> omega

theorem size_eq_pow : EvmYul.UInt256.size = 2 ^ 256 := rfl

private theorem toNat_neg_one (x : EvmYul.UInt256) :
    wordNat (⟨x.val * (-1)⟩ : EvmYul.UInt256)
      = (EvmYul.UInt256.size - wordNat x) % EvmYul.UInt256.size := by
  have hrw : (x.val * (-1)) = (0 - x.val) := by rw [mul_neg_one, zero_sub]
  rw [show (⟨x.val * (-1)⟩ : EvmYul.UInt256) = ⟨0 - x.val⟩ from congrArg _ hrw]
  simp only [wordNat, EvmYul.UInt256.toNat, Fin.sub_def, Fin.val_zero, EvmYul.UInt256.size]
  omega

private theorem wordNat_abs (a : EvmYul.UInt256) :
    wordNat (EvmYul.UInt256.abs a)
      = if 2 ^ 255 ≤ wordNat a then (EvmYul.UInt256.size - wordNat a) % EvmYul.UInt256.size
        else wordNat a := by
  show (EvmYul.UInt256.abs a).toNat
      = if 2 ^ 255 ≤ a.toNat then (EvmYul.UInt256.size - a.toNat) % EvmYul.UInt256.size
        else a.toNat
  unfold EvmYul.UInt256.abs
  by_cases h : 2 ^ 255 ≤ a.toNat
  · simp only [if_pos h]; exact toNat_neg_one a
  · simp only [if_neg h]

theorem wordNat_sdiv (a b : EvmYul.UInt256) :
    wordNat (EvmYul.UInt256.sdiv a b) = evmSdiv (wordNat a) (wordNat b) := by
  have ha : wordNat a < 2 ^ 256 := by
    simp [EvmYul.UInt256.toNat, EvmYul.UInt256.size, wordNat]
  have hb : wordNat b < 2 ^ 256 := by
    simp [EvmYul.UInt256.toNat, EvmYul.UInt256.size, wordNat]
  have hua : u256 (wordNat a) = wordNat a := by unfold u256 WORD_MOD; exact Nat.mod_eq_of_lt ha
  have hub : u256 (wordNat b) = wordNat b := by unfold u256 WORD_MOD; exact Nat.mod_eq_of_lt hb
  have hwm : WORD_MOD = 2 ^ 256 := word_mod_eq
  have hsz : EvmYul.UInt256.size = 2 ^ 256 := size_eq_pow
  simp only [evmSdiv, hua, hub, hwm]
  unfold EvmYul.UInt256.sdiv
  by_cases hna : 2 ^ 255 ≤ wordNat a <;> by_cases hnb : 2 ^ 255 ≤ wordNat b
  · have dna : decide (2 ^ 255 ≤ wordNat a) = true := decide_eq_true_eq.mpr hna
    have dnb : decide (2 ^ 255 ≤ wordNat b) = true := decide_eq_true_eq.mpr hnb
    have m1 : (2 ^ 256 - wordNat a) % 2 ^ 256 = 2 ^ 256 - wordNat a := Nat.mod_eq_of_lt (by omega)
    have m2 : (2 ^ 256 - wordNat b) % 2 ^ 256 = 2 ^ 256 - wordNat b := Nat.mod_eq_of_lt (by omega)
    rw [if_pos (show 2 ^ 255 ≤ a.toNat from hna), if_pos (show 2 ^ 255 ≤ b.toNat from hnb),
      wordNat_div, wordNat_abs, wordNat_abs, hsz, if_pos hna, if_pos hnb]
    simp only [dna, dnb, if_true]
    simp only [evmDiv, u256, WORD_MOD, m1, m2]
    have hq : (2 ^ 256 - wordNat a) / (2 ^ 256 - wordNat b) ≤ 2 ^ 256 - wordNat a := Nat.div_le_self _ _
    revert hq
    generalize (2 ^ 256 - wordNat a) / (2 ^ 256 - wordNat b) = q
    intro hq
    split_ifs <;> omega
  · have dna : decide (2 ^ 255 ≤ wordNat a) = true := decide_eq_true_eq.mpr hna
    have dnb : decide (2 ^ 255 ≤ wordNat b) = false := decide_eq_false_iff_not.mpr hnb
    have m1 : (2 ^ 256 - wordNat a) % 2 ^ 256 = 2 ^ 256 - wordNat a := Nat.mod_eq_of_lt (by omega)
    have hmodb : wordNat b % 2 ^ 256 = wordNat b := Nat.mod_eq_of_lt hb
    rw [if_pos (show 2 ^ 255 ≤ a.toNat from hna), if_neg (show ¬ 2 ^ 255 ≤ b.toNat from hnb),
      toNat_neg_one, hsz, wordNat_div, wordNat_abs, hsz, if_pos hna]
    simp only [dna, dnb, Bool.true_eq_false, Bool.false_eq_true,
      if_true, if_false]
    simp only [evmDiv, u256, WORD_MOD, m1, hmodb]
    have hq : (2 ^ 256 - wordNat a) / wordNat b ≤ 2 ^ 256 - wordNat a := Nat.div_le_self _ _
    revert hq
    generalize (2 ^ 256 - wordNat a) / wordNat b = q
    intro hq
    split_ifs <;> omega
  · have dna : decide (2 ^ 255 ≤ wordNat a) = false := decide_eq_false_iff_not.mpr hna
    have dnb : decide (2 ^ 255 ≤ wordNat b) = true := decide_eq_true_eq.mpr hnb
    have m2 : (2 ^ 256 - wordNat b) % 2 ^ 256 = 2 ^ 256 - wordNat b := Nat.mod_eq_of_lt (by omega)
    have hmoda : wordNat a % 2 ^ 256 = wordNat a := Nat.mod_eq_of_lt ha
    rw [if_neg (show ¬ 2 ^ 255 ≤ a.toNat from hna), if_pos (show 2 ^ 255 ≤ b.toNat from hnb),
      toNat_neg_one, hsz, wordNat_div, wordNat_abs, hsz, if_pos hnb]
    simp only [dna, dnb, Bool.false_eq_true,
      if_true, if_false]
    simp only [evmDiv, u256, WORD_MOD, m2, hmoda]
    have hq : wordNat a / (2 ^ 256 - wordNat b) ≤ wordNat a := Nat.div_le_self _ _
    revert hq
    generalize wordNat a / (2 ^ 256 - wordNat b) = q
    intro hq
    split_ifs <;> omega
  · have dna : decide (2 ^ 255 ≤ wordNat a) = false := decide_eq_false_iff_not.mpr hna
    have dnb : decide (2 ^ 255 ≤ wordNat b) = false := decide_eq_false_iff_not.mpr hnb
    have hmoda : wordNat a % 2 ^ 256 = wordNat a := Nat.mod_eq_of_lt ha
    have hmodb : wordNat b % 2 ^ 256 = wordNat b := Nat.mod_eq_of_lt hb
    rw [if_neg (show ¬ 2 ^ 255 ≤ a.toNat from hna), if_neg (show ¬ 2 ^ 255 ≤ b.toNat from hnb),
      wordNat_div]
    simp only [dna, dnb, Bool.false_eq_true,
      if_true, if_false]
    simp only [evmDiv, u256, WORD_MOD, hmoda, hmodb]
    have hq : wordNat a / wordNat b ≤ wordNat a := Nat.div_le_self _ _
    revert hq
    generalize wordNat a / wordNat b = q
    intro hq
    split_ifs <;> omega

theorem wordNat_slt (a b : EvmYul.UInt256) :
    wordNat (EvmYul.UInt256.slt a b) = evmSlt (wordNat a) (wordNat b) := by
  have ha : a.toNat < 2 ^ 256 := by simp [EvmYul.UInt256.toNat, EvmYul.UInt256.size]
  have hb : b.toNat < 2 ^ 256 := by simp [EvmYul.UInt256.toNat, EvmYul.UInt256.size]
  have hua : u256 (wordNat a) = wordNat a := by unfold u256 WORD_MOD; exact Nat.mod_eq_of_lt ha
  have hub : u256 (wordNat b) = wordNat b := by unfold u256 WORD_MOD; exact Nat.mod_eq_of_lt hb
  have hlt2 : (a < b) ↔ (a.toNat < b.toNat) := Iff.rfl
  -- Offset (excess-2^255) values of the two operands, in closed form per sign.
  have offneg : ∀ c : Nat, c < 2 ^ 256 → 2 ^ 255 ≤ c →
      (c + 2 ^ 255) % 2 ^ 256 = c - 2 ^ 255 := by
    intro c hc hcn
    rw [show c + 2 ^ 255 = (c - 2 ^ 255) + 2 ^ 256 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  have offpos : ∀ c : Nat, c < 2 ^ 256 → c < 2 ^ 255 →
      (c + 2 ^ 255) % 2 ^ 256 = c + 2 ^ 255 := by
    intro c hc hcp; exact Nat.mod_eq_of_lt (by omega)
  have key : EvmYul.UInt256.sltBool a b =
      decide ((a.toNat + 2 ^ 255) % 2 ^ 256 < (b.toNat + 2 ^ 255) % 2 ^ 256) := by
    unfold EvmYul.UInt256.sltBool
    simp only [ge_iff_le]
    by_cases hna : 2 ^ 255 ≤ a.toNat <;> by_cases hnb : 2 ^ 255 ≤ b.toNat
    · rw [if_pos hna, if_pos hnb, offneg _ ha hna, offneg _ hb hnb]
      apply decide_eq_decide.mpr; rw [hlt2]; omega
    · rw [if_pos hna, if_neg hnb, offneg _ ha hna, offpos _ hb (by omega), eq_comm,
        decide_eq_true_eq]; omega
    · rw [if_neg hna, if_pos hnb, offpos _ ha (by omega), offneg _ hb hnb, eq_comm,
        decide_eq_false_iff_not]; omega
    · rw [if_neg hna, if_neg hnb, offpos _ ha (by omega), offpos _ hb (by omega)]
      apply decide_eq_decide.mpr; rw [hlt2]; omega
  have hLHS : wordNat (EvmYul.UInt256.slt a b) =
      if (a.toNat + 2 ^ 255) % 2 ^ 256 < (b.toNat + 2 ^ 255) % 2 ^ 256 then 1 else 0 := by
    unfold EvmYul.UInt256.slt
    rw [key]
    simp only [EvmYul.fromBool, Bool.toUInt256, decide_eq_true_eq]
    split_ifs <;> decide
  have hua' : u256 (wordNat a) = a.toNat := hua
  have hub' : u256 (wordNat b) = b.toNat := hub
  have hRHS : evmSlt (wordNat a) (wordNat b) =
      if (a.toNat + 2 ^ 255) % 2 ^ 256 < (b.toNat + 2 ^ 255) % 2 ^ 256 then 1 else 0 := by
    unfold evmSlt
    rw [hua', hub', word_mod_eq]
  rw [hLHS, hRHS]

/-- An `evmAdd` result is already `u256`-wrapped, so injecting it through `ofNat` and reading its
`toNat` is the identity. Discharges the run-level `resultWord` extraction without re-stating the
evm* tree. -/
theorem toNat_ofNat_evmAdd (a b : Nat) :
    (EvmYul.UInt256.ofNat (evmAdd a b)).toNat = evmAdd a b := by
  change wordNat (EvmYul.UInt256.ofNat (evmAdd a b)) = evmAdd a b
  rw [FormalYul.Preservation.wordNat_ofNat]
  exact FormalYul.Preservation.u256_evmAdd a b

theorem evmSlt_u256_left (a b : Nat) : evmSlt (u256 a) b = evmSlt a b := by
  simp only [evmSlt, u256_idem]
theorem evmSlt_u256_right (a b : Nat) : evmSlt a (u256 b) = evmSlt a b := by
  simp only [evmSlt, u256_idem]

theorem evmSar_u256_left (s v : Nat) : evmSar (u256 s) v = evmSar s v := by
  simp only [evmSar, u256_idem]
theorem evmSar_u256_right (s v : Nat) : evmSar s (u256 v) = evmSar s v := by
  simp only [evmSar, u256_idem]
theorem evmSdiv_u256_left (a b : Nat) : evmSdiv (u256 a) b = evmSdiv a b := by
  simp only [evmSdiv, u256_idem]
theorem evmSdiv_u256_right (a b : Nat) : evmSdiv a (u256 b) = evmSdiv a b := by
  simp only [evmSdiv, u256_idem]

end Common.Word
