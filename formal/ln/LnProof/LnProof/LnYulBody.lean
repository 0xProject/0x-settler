import LnProof.LnYulProof
import FormalYul.Preservation
import LnProof.Stages
import LnProof.Bridge
import LnProof.BridgeDiv
import LnProof.TopMono

/-!
# Runtime ↔ model equivalence (Part B), building blocks

Toward proving that the compiled `LnWrapper` runtime computes the hand model
`Stages.lnWadToRayBody` / `Stages.lnWadBody`. This file establishes the
arithmetic facts that drive the revert guard `if iszero(slt(0, x))` in
`fun_lnWadToRay_11`: for a positive signed input the guard is skipped, for a
nonpositive one it is taken.
-/

namespace LnYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

theorem u256_lt_word (x : Nat) : u256 x < 2 ^ 256 := by
  unfold u256 WORD_MOD
  exact Nat.mod_lt _ (Nat.two_pow_pos 256)

theorem u256_idem (x : Nat) : u256 (u256 x) = u256 x := by
  unfold u256 WORD_MOD
  exact Nat.mod_mod_of_dvd x (dvd_refl _)

/-- A positive signed input has its low 256 bits in `[1, 2^255)`. -/
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

/-- The revert guard `slt(0, x)` is `1` for a positive signed input, so
`iszero(slt(0, x))` is `0` and the guard branch is skipped. -/
theorem evmSlt_zero_pos {x : Nat} (h1 : 1 ≤ u256 x) (h2 : u256 x < 2 ^ 255) :
    evmSlt 0 (u256 x) = 1 := by
  unfold evmSlt
  have h0 : u256 0 = 0 := by unfold u256 WORD_MOD; simp
  have hidem : u256 (u256 x) = u256 x := u256_idem x
  rw [h0, hidem]
  have hmod1 : (0 + 2 ^ 255) % WORD_MOD = 2 ^ 255 := by
    unfold WORD_MOD; omega
  have hmod2 : (u256 x + 2 ^ 255) % WORD_MOD = u256 x + 2 ^ 255 := by
    unfold WORD_MOD; omega
  rw [hmod1, hmod2]
  rw [if_pos (by omega)]

/-- The revert guard `slt(0, x)` is `0` for a nonpositive signed input, so
`iszero(slt(0, x))` is `1` and the guard branch (revert) is taken. -/
theorem evmSlt_zero_nonpos {x : Nat} (h : int256 (u256 x) ≤ 0) :
    evmSlt 0 (u256 x) = 0 := by
  have hlt : u256 x < 2 ^ 256 := u256_lt_word x
  unfold evmSlt
  have h0 : u256 0 = 0 := by unfold u256 WORD_MOD; simp
  have hidem : u256 (u256 x) = u256 x := u256_idem x
  rw [h0, hidem]
  have hmod1 : (0 + 2 ^ 255) % WORD_MOD = 2 ^ 255 := by
    unfold WORD_MOD; omega
  rw [hmod1]
  -- nonpositive int256 ⇒ either u256 x = 0, or u256 x ≥ 2^255
  have hcases : u256 x = 0 ∨ 2 ^ 255 ≤ u256 x := by
    by_contra hc
    push_neg at hc
    obtain ⟨hne, hge⟩ := hc
    have hpos : 0 < u256 x := Nat.pos_of_ne_zero hne
    unfold int256 at h
    simp only [hge, if_true] at h
    have : (0 : Int) < u256 x := by exact_mod_cast hpos
    omega
  rcases hcases with h0x | hge
  · rw [h0x]; unfold WORD_MOD; simp
  · have hmod2 : (u256 x + 2 ^ 255) % WORD_MOD = u256 x - 2 ^ 255 := by
      unfold WORD_MOD; omega
    rw [hmod2]
    rw [if_neg (by omega)]

/-- `slt(0, x)` evaluates to the word `1` for a positive signed input, which is
exactly what the interpreter needs to skip the `if iszero(slt(0, x))` revert
guard in `fun_lnWadToRay_11`. -/
theorem slt_zero_pos {x : Nat} (h1 : 1 ≤ u256 x) (h2 : u256 x < 2 ^ 255) :
    EvmYul.UInt256.slt (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat x)
      = EvmYul.UInt256.ofNat 1 := by
  have hx : (EvmYul.UInt256.ofNat x).toNat = u256 x := by
    have := wordNat_ofNat x; simpa [wordNat] using this
  have h0 : (EvmYul.UInt256.ofNat 0).toNat = 0 := by
    have := wordNat_ofNat 0; simpa [wordNat, u256, WORD_MOD] using this
  have hlt : EvmYul.UInt256.ofNat 0 < EvmYul.UInt256.ofNat x := by
    have hh : (EvmYul.UInt256.ofNat 0).toNat < (EvmYul.UInt256.ofNat x).toNat := by
      rw [h0, hx]; omega
    exact hh
  have c1 : ¬ ((0 : Nat) ≥ 2 ^ 255) := by omega
  have c2 : ¬ (u256 x ≥ 2 ^ 255) := by omega
  unfold EvmYul.UInt256.slt EvmYul.UInt256.sltBool
  rw [hx, h0, if_neg c1, if_neg c2]
  simp [EvmYul.UInt256.fromBool, hlt]

/-- `slt(0, x)` evaluates to the word `0` for a nonpositive signed input, so the
interpreter takes the `if iszero(slt(0, x))` revert guard in `fun_lnWadToRay_11`. -/
theorem slt_zero_nonpos {x : Nat} (hnonpos : int256 (u256 x) ≤ 0) :
    EvmYul.UInt256.slt (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat x)
      = EvmYul.UInt256.ofNat 0 := by
  have hlt256 : u256 x < 2 ^ 256 := u256_lt_word x
  have hx : (EvmYul.UInt256.ofNat x).toNat = u256 x := by
    have := wordNat_ofNat x; simpa [wordNat] using this
  have h0 : (EvmYul.UInt256.ofNat 0).toNat = 0 := by
    have := wordNat_ofNat 0; simpa [wordNat, u256, WORD_MOD] using this
  have hcases : u256 x = 0 ∨ 2 ^ 255 ≤ u256 x := by
    by_contra hc
    push_neg at hc
    obtain ⟨hne, hge⟩ := hc
    have hpos : 0 < u256 x := Nat.pos_of_ne_zero hne
    unfold int256 at hnonpos
    simp only [hge, if_true] at hnonpos
    have : (0 : Int) < u256 x := by exact_mod_cast hpos
    omega
  unfold EvmYul.UInt256.slt EvmYul.UInt256.sltBool
  rw [hx, h0, if_neg (by omega : ¬ ((0 : Nat) ≥ 2 ^ 255))]
  rcases hcases with h0x | hge
  · rw [if_neg (by rw [h0x]; omega : ¬ (u256 x ≥ 2 ^ 255))]
    have hnlt : ¬ EvmYul.UInt256.ofNat 0 < EvmYul.UInt256.ofNat x := by
      show ¬ (EvmYul.UInt256.ofNat 0).toNat < (EvmYul.UInt256.ofNat x).toNat
      rw [h0, hx, h0x]; omega
    simp [EvmYul.UInt256.fromBool, hnlt]
  · rw [if_pos (by omega : u256 x ≥ 2 ^ 255)]
    simp [EvmYul.UInt256.fromBool]

/-- `wordNat` of `UInt256.complement` is `evmNot` (the complement equals the
two's-complement bitwise-not at the `Nat` level). -/
theorem wordNat_complement (a : EvmYul.UInt256) :
    wordNat (EvmYul.UInt256.complement a) = evmNot (wordNat a) := by
  have hav : a.toNat < 2 ^ 256 := by
    simp [EvmYul.UInt256.toNat, EvmYul.UInt256.size]
  simp only [wordNat, EvmYul.UInt256.complement, EvmYul.UInt256.toNat, evmNot, u256, WORD_MOD,
    Fin.sub_def, Fin.add_def, Fin.val_zero, Fin.val_one, EvmYul.UInt256.size]
  omega

/-- Arithmetic-shift-right bridge: `UInt256.sar` matches `evmSar`. Uses the
decomposition `sar = complement (complement b >>> a)` (for negative `b`) and
`b >>> a` (otherwise), composing `wordNat_complement` + `wordNat_shiftRight`. -/
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

/-- `UInt256.size = 2^256`, kept in `Nat.pow` form (never the 78-digit literal,
which would force kernel deep-recursion). -/
theorem size_eq_pow : EvmYul.UInt256.size = 2 ^ 256 := rfl

/-- `toNat` of the Fin negation `⟨x.val * (-1)⟩`. Routed through Fin
*subtraction* (`0 - x.val`, recursion-free like `complement`) rather than
Fin `Mul`/`Neg`, whose instances force kernel materialization of `2^256`. -/
private theorem toNat_neg_one (x : EvmYul.UInt256) :
    wordNat (⟨x.val * (-1)⟩ : EvmYul.UInt256)
      = (EvmYul.UInt256.size - wordNat x) % EvmYul.UInt256.size := by
  have hrw : (x.val * (-1)) = (0 - x.val) := by rw [mul_neg_one, zero_sub]
  rw [show (⟨x.val * (-1)⟩ : EvmYul.UInt256) = ⟨0 - x.val⟩ from congrArg _ hrw]
  simp only [wordNat, EvmYul.UInt256.toNat, Fin.sub_def, Fin.val_zero, EvmYul.UInt256.size]
  omega

/-- `toNat` of `UInt256.abs` (two's-complement absolute value). -/
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

/-- Signed-division bridge: `UInt256.sdiv` matches `evmSdiv`. Four sign cases
(`2^255 ≤ a/b.toNat`), using `wordNat_abs`/`toNat_neg_one` for the abs and
negated arms; all powers kept as `2^n` to avoid kernel literal materialization. -/
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
  · -- a < 0, b < 0
    have dna : decide (2 ^ 255 ≤ wordNat a) = true := decide_eq_true_eq.mpr hna
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
  · -- a < 0, b ≥ 0
    have dna : decide (2 ^ 255 ≤ wordNat a) = true := decide_eq_true_eq.mpr hna
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
  · -- a ≥ 0, b < 0
    have dna : decide (2 ^ 255 ≤ wordNat a) = false := decide_eq_false_iff_not.mpr hna
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
  · -- a ≥ 0, b ≥ 0
    have dna : decide (2 ^ 255 ≤ wordNat a) = false := decide_eq_false_iff_not.mpr hna
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

/-- The `zero_value_for_split_t_int256()` helper returns the word `0`. -/
private theorem call_zero_value_for_split_t_int256_direct
    (fuel extra : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + (extra + 20)) [] (.some "zero_value_for_split_t_int256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word 0]) := by
  rw [show fuel + (extra + 20) = (fuel + extra) + 20 by omega]
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_zero_value_for_split_t_int256]
  simp only [yulFunction_zero_value_for_split_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

private theorem evmSar_u256_left (s v : Nat) : evmSar (u256 s) v = evmSar s v := by
  simp only [evmSar, u256_idem]
private theorem evmSar_u256_right (s v : Nat) : evmSar s (u256 v) = evmSar s v := by
  simp only [evmSar, u256_idem]
private theorem evmSdiv_u256_left (a b : Nat) : evmSdiv (u256 a) b = evmSdiv a b := by
  simp only [evmSdiv, u256_idem]
private theorem evmSdiv_u256_right (a b : Nat) : evmSdiv a (u256 b) = evmSdiv a b := by
  simp only [evmSdiv, u256_idem]
private theorem evmSgt_u256_left (a b : Nat) : evmSgt (u256 a) b = evmSgt a b := by
  simp only [evmSgt, u256_idem]
private theorem evmSgt_u256_right (a b : Nat) : evmSgt a (u256 b) = evmSgt a b := by
  simp only [evmSgt, u256_idem]

/-- `wordNat` of `UInt256.sgt 0 r` matches `evmSgt 0 (wordNat r)`. Only the
zero-left case is needed: the `mul(999999999, sgt(0, r))` rounding term in
`fun_lnWad_27`. -/
theorem wordNat_sgt_zero (r : EvmYul.UInt256) :
    wordNat (EvmYul.UInt256.sgt (EvmYul.UInt256.ofNat 0) r) = evmSgt 0 (wordNat r) := by
  have hr : wordNat r < 2 ^ 256 := by
    simp [EvmYul.UInt256.toNat, EvmYul.UInt256.size, wordNat]
  have h0 : (EvmYul.UInt256.ofNat 0).toNat = 0 := by
    have := FormalYul.Preservation.wordNat_ofNat 0
    simpa [wordNat, u256, WORD_MOD] using this
  unfold evmSgt
  have hu0 : u256 0 = 0 := by unfold u256 WORD_MOD; simp
  have hur : u256 (wordNat r) = wordNat r := by unfold u256 WORD_MOD; exact Nat.mod_eq_of_lt hr
  rw [hu0, hur]
  have hm0 : (0 + 2 ^ 255) % WORD_MOD = 2 ^ 255 := by unfold WORD_MOD; omega
  rw [hm0]
  unfold EvmYul.UInt256.sgt EvmYul.UInt256.sgtBool
  rw [show (EvmYul.UInt256.ofNat 0).toNat = 0 from h0]
  rw [if_neg (by omega : ¬ (0 : Nat) ≥ 2 ^ 255)]
  by_cases hb : r.toNat ≥ 2 ^ 255
  · rw [if_pos hb]
    have hlt : (wordNat r + 2 ^ 255) % WORD_MOD < 2 ^ 255 := by
      unfold WORD_MOD wordNat; unfold wordNat at hr; omega
    rw [if_pos hlt]; rfl
  · rw [if_neg hb]
    have hgt : ¬ (EvmYul.UInt256.ofNat 0) > r := by
      show ¬ (r < EvmYul.UInt256.ofNat 0)
      show ¬ (r.toNat < (EvmYul.UInt256.ofNat 0).toNat)
      rw [h0]; omega
    have hnlt : ¬ (wordNat r + 2 ^ 255) % WORD_MOD < 2 ^ 255 := by
      unfold WORD_MOD wordNat; unfold wordNat at hr; omega
    rw [if_neg hnlt]
    simp [EvmYul.UInt256.fromBool, hgt, wordNat, h0]

/-- `lnWadBody` as an explicit expression over the opaque `lnWadToRayBody x`
(the interpreter's reduced sdiv tail). `rfl` since it is the `let`-unfolding of
the `lnWadBody` definition; `lnWadToRayBody x` is never materialized. -/
theorem lnWadCoreExpr_eq (x : Nat) :
    evmSdiv (evmSub (lnWadToRayBody x)
        (evmMul 999999999 (evmSgt 0 (lnWadToRayBody x)))) 1000000000 =
      lnWadBody x := rfl

/-- The hand model `lnWadToRayBody`, written as an explicit `let`-shared expression
matching the interpreter's reduced form. Both sides are `let`-shared (linear), so the
`rfl` is cheap and never materializes the (exponential) inlined tree. -/
theorem lnWadToRayCoreExpr_eq (x : Nat) :
    (let c := evmClz x
     let k := evmSub 160 c
     let m := evmShr 160 (evmShl c x)
     let z := evmSdiv (evmShl 100 (evmSub Sc m)) (evmAdd m Sc)
     let u := evmShr 104 (evmMul z z)
     let p := evmAdd (evmSar 87 (evmMul (evmSub (evmSar 97 (evmMul (evmAdd (evmSar 90
       (evmMul (evmSub (evmShr 84 (evmMul P4c u)) P3c) u)) P2c) u)) P1c) u)) C0c
     let q := evmSub (evmSar 95 (evmMul (evmAdd (evmSar 88 (evmMul (evmSub (evmSar 90
       (evmMul (evmAdd (evmSar 113 (evmMul (evmSub u Q4c) u)) Q3c) u)) Q2c) u)) Q1c) u)) C0c
     let r0 := evmSdiv (evmMul p z) q
     let r1 := evmMul Kc r0
     let r2 := evmAdd (evmMul LN2c k) r1
     let r3 := evmAdd BIASc r2
     let r4 := evmSar 72 r3
     evmAdd (evmIszero (evmNot r4)) r4) = lnWadToRayBody x := by
  unfold lnWadToRayBody zWord uWord pS4 pS3 pS2 pS1 qS5 qS4 qS3 qS2 qS1
  rfl

set_option maxHeartbeats 8000000 in
/-- The compiled `fun_lnWadToRay_11` computes the model `lnWadToRayBody` for a
positive signed input (the leading `if iszero(slt(0,x))` revert guard is skipped). -/
theorem call_fun_lnWadToRay_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hpos : 1 ≤ FormalYul.u256 x) (hpos2 : FormalYul.u256 x < 2 ^ 255) :
    EvmYul.Yul.call (fuel + 600) [FormalYul.word x] (.some yulName_fun_lnWadToRay)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (lnWadToRayBody (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_lnWadToRay]
  simp only [yulFunction_fun_lnWadToRay, yulFunction_fun_lnWadToRay_11,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word,
    slt_zero_pos hpos hpos2,
    call_zero_value_for_split_t_int256_direct (fuel := fuel) (extra := 576)
      (shared := shared)
      (store := Finmap.insert "var_x_4" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_shiftRight, FormalYul.Preservation.wordNat_shiftLeft,
    FormalYul.Preservation.wordNat_add, FormalYul.Preservation.wordNat_sub,
    FormalYul.Preservation.wordNat_mul, FormalYul.Preservation.wordNat_clz,
    FormalYul.Preservation.wordNat_iszero, FormalYul.Preservation.wordNat_not,
    FormalYul.Preservation.wordNat_ofNat, wordNat_sar, wordNat_sdiv]
  simpa only [FormalYul.Preservation.evmAdd_u256_left, FormalYul.Preservation.evmAdd_u256_right,
    FormalYul.Preservation.evmSub_u256_left, FormalYul.Preservation.evmSub_u256_right,
    FormalYul.Preservation.evmMul_u256_left, FormalYul.Preservation.evmMul_u256_right,
    FormalYul.Preservation.evmShl_u256_left, FormalYul.Preservation.evmShl_u256_right,
    FormalYul.Preservation.evmShr_u256_left, FormalYul.Preservation.evmShr_u256_right,
    FormalYul.Preservation.evmClz_u256, FormalYul.Preservation.evmIszero_u256,
    FormalYul.Preservation.evmNot_u256, evmSar_u256_left, evmSar_u256_right,
    evmSdiv_u256_left, evmSdiv_u256_right, u256_u256, u256_idem,
    FormalYul.Preservation.u256_eq_of_lt _ (lnWadToRayBody_lt (u256_lt_word x)),
    Sc, P4c, P3c, P2c, P1c, C0c, Q4c, Q3c, Q2c, Q1c, Kc, LN2c, BIASc]
    using lnWadToRayCoreExpr_eq (FormalYul.u256 x)

/-- A Yul `revert(a, b)` primitive call halts with `.error .Revert` (the
`MachineState.evmRevert` op is total, so the `Semantics` dispatch always reaches
the `.ok ⇒ .error .Revert` branch). Mirror of the `primCall_*` lemmas. -/
private theorem primCall_revert_yul (fuel : Nat) (s : EvmYul.Yul.State)
    (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s
        (EvmYul.Operation.System EvmYul.Operation.SOp.REVERT : EvmYul.Operation .Yul) [a, b] =
      .error EvmYul.Yul.Exception.Revert := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, List.not_mem_nil, EvmYul.Operation.System.injEq,
    Bool.not_eq_true, reduceCtorEq, or_self, and_false, if_false,
    EvmYul.step.eq_def]
  rfl

set_option maxHeartbeats 8000000 in
theorem call_fun_lnWadToRay_revert_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hnonpos : int256 (FormalYul.u256 x) ≤ 0) :
    EvmYul.Yul.call (fuel + 600) [FormalYul.word x] (.some yulName_fun_lnWadToRay)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .error EvmYul.Yul.Exception.Revert := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_lnWadToRay]
  simp only [yulFunction_fun_lnWadToRay, yulFunction_fun_lnWadToRay_11,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.setStore,
    FormalYul.word,
    slt_zero_nonpos hnonpos, primCall_revert_yul,
    call_zero_value_for_split_t_int256_direct (fuel := fuel) (extra := 576)
      (shared := shared)
      (store := Finmap.insert "var_x_4" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]

set_option maxHeartbeats 8000000 in
theorem call_fun_wrap_lnWadToRay_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hpos : 1 ≤ FormalYul.u256 x) (hpos2 : FormalYul.u256 x < 2 ^ 255) :
    EvmYul.Yul.call (fuel + 800) [FormalYul.word x] (.some yulName_fun_wrap_lnWadToRay)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (lnWadToRayBody (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_wrap_lnWadToRay]
  simp only [yulFunction_fun_wrap_lnWadToRay, yulFunction_fun_wrap_lnWadToRay_46,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hfuel : fuel + 791 = (fuel + 191) + 600 := by omega
  have hCall := call_fun_lnWadToRay_direct (x := x) (fuel := fuel + 191) (shared := shared)
    (store := Finmap.insert "expr_42" (EvmYul.UInt256.ofNat x)
      (Finmap.insert "_4" (EvmYul.UInt256.ofNat x)
        (Finmap.insert "expr_40_address" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "var__38" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "zero_t_int256_3" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "var_x_35" (EvmYul.UInt256.ofNat x)
                (Inhabited.default : EvmYul.Yul.VarStore)))))))
    (hlookup := hlookup) hpos hpos2
  simp only [FormalYul.word, yulName_fun_lnWadToRay] at hCall
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.setLeave,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hfuel, hCall,
    call_zero_value_for_split_t_int256_direct (fuel := fuel) (extra := 776)
      (shared := shared)
      (store := Finmap.insert "var_x_35" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]

set_option maxHeartbeats 8000000 in
theorem call_fun_lnWad_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hpos : 1 ≤ FormalYul.u256 x) (hpos2 : FormalYul.u256 x < 2 ^ 255) :
    EvmYul.Yul.call (fuel + 900) [FormalYul.word x] (.some yulName_fun_lnWad)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (lnWadBody (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_lnWad]
  simp only [yulFunction_fun_lnWad, yulFunction_fun_lnWad_27,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hfuel : fuel + 892 = (fuel + 292) + 600 := by omega
  have hCall := call_fun_lnWadToRay_direct (x := x) (fuel := fuel + 292) (shared := shared)
    (store := Finmap.insert "expr_21" (EvmYul.UInt256.ofNat x)
      (Finmap.insert "_6" (EvmYul.UInt256.ofNat x)
        (Finmap.insert "var_r_17" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "zero_t_int256_5" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "var_x_14" (EvmYul.UInt256.ofNat x)
              (Inhabited.default : EvmYul.Yul.VarStore))))))
    (hlookup := hlookup) hpos hpos2
  simp only [FormalYul.word, yulName_fun_lnWadToRay] at hCall
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hfuel, hCall,
    call_zero_value_for_split_t_int256_direct (fuel := fuel) (extra := 876)
      (shared := shared)
      (store := Finmap.insert "var_x_14" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]
  apply FormalYul.Preservation.eq_of_wordNat_eq
  simp only [FormalYul.Preservation.wordNat_sub, FormalYul.Preservation.wordNat_mul,
    wordNat_sdiv, wordNat_sgt_zero, FormalYul.Preservation.wordNat_ofNat]
  simpa only [evmSdiv_u256_left, evmSdiv_u256_right,
    FormalYul.Preservation.evmSub_u256_left, FormalYul.Preservation.evmSub_u256_right,
    FormalYul.Preservation.evmMul_u256_left, FormalYul.Preservation.evmMul_u256_right,
    evmSgt_u256_left, evmSgt_u256_right, u256_u256, u256_idem,
    FormalYul.Preservation.u256_eq_of_lt _ (lnWadToRayBody_lt (u256_lt_word x)),
    FormalYul.Preservation.u256_eq_of_lt _ (to_wad_lt (u256_lt_word x))]
    using lnWadCoreExpr_eq (FormalYul.u256 x)

set_option maxHeartbeats 8000000 in
theorem call_fun_wrap_lnWad_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hpos : 1 ≤ FormalYul.u256 x) (hpos2 : FormalYul.u256 x < 2 ^ 255) :
    EvmYul.Yul.call (fuel + 1100) [FormalYul.word x] (.some yulName_fun_wrap_lnWad)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [FormalYul.word (lnWadBody (FormalYul.u256 x))]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_wrap_lnWad]
  simp only [yulFunction_fun_wrap_lnWad, yulFunction_fun_wrap_lnWad_59,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hfuel : fuel + 1091 = (fuel + 191) + 900 := by omega
  have hCall := call_fun_lnWad_direct (x := x) (fuel := fuel + 191) (shared := shared)
    (store := Finmap.insert "expr_55" (EvmYul.UInt256.ofNat x)
      (Finmap.insert "_2" (EvmYul.UInt256.ofNat x)
        (Finmap.insert "expr_53_address" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "var__51" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "zero_t_int256_1" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "var_x_48" (EvmYul.UInt256.ofNat x)
                (Inhabited.default : EvmYul.Yul.VarStore)))))))
    (hlookup := hlookup) hpos hpos2
  simp only [FormalYul.word, yulName_fun_lnWad] at hCall
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.revive, EvmYul.Yul.State.setLeave,
    EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hfuel, hCall,
    call_zero_value_for_split_t_int256_direct (fuel := fuel) (extra := 1076)
      (shared := shared)
      (store := Finmap.insert "var_x_48" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]

/-- Shared state after the dispatcher's `mstore(64,128)` free-pointer init, for the
lnWadToRay calldata. Port of cbrt's `cbrtSharedAfterFreePtr`. -/
private def lnWadToRaySharedAfterFreePtr (x : Nat) : EvmYul.SharedState .Yul :=
  let shared := FormalYul.sharedFor yulContract (selector_lnWadToRay ++ FormalYul.encodeWords [x])
  { shared with toMachineState := shared.toMachineState.mstore (FormalYul.word 64) (FormalYul.word 128) }

@[simp]
private theorem lnWadToRaySharedAfterFreePtr_lookup (x : Nat) :
    (lnWadToRaySharedAfterFreePtr x).accountMap.find?
        (lnWadToRaySharedAfterFreePtr x).executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract) := by
  simp [lnWadToRaySharedAfterFreePtr]

@[simp]
private theorem lnWadToRaySharedAfterFreePtr_calldata (x : Nat) :
    (lnWadToRaySharedAfterFreePtr x).executionEnv.calldata =
      selector_lnWadToRay ++ FormalYul.encodeWords [x] := by
  simp [lnWadToRaySharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp]
private theorem lnWadToRaySharedAfterFreePtr_weiValue (x : Nat) :
    (lnWadToRaySharedAfterFreePtr x).executionEnv.weiValue = ({ val := 0 } : EvmYul.UInt256) := by
  simp [lnWadToRaySharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp]
private theorem lnWadToRaySharedAfterFreePtr_mload64 (x : Nat) :
    ((lnWadToRaySharedAfterFreePtr x).mload (FormalYul.word 64)).1 = FormalYul.word 128 :=
  FormalYul.Preservation.sharedFor_mload_freePtr_after_mstore yulContract
    (selector_lnWadToRay ++ FormalYul.encodeWords [x])

@[simp]
private theorem lnWadToRay_calldata_size (x : Nat) :
    (selector_lnWadToRay ++ FormalYul.encodeWords [x]).size = 36 := by
  simp [selector_lnWadToRay, FormalYul.encodeWords,
    FormalYul.bytes, ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
    FormalYul.Preservation.encodeWord_size]

@[simp]
private theorem calldataload_lnWadToRay_arg_of_calldata
    (x : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hdata : shared.executionEnv.calldata = selector_lnWadToRay ++ FormalYul.encodeWords [x]) :
    EvmYul.State.calldataload
      (EvmYul.Yul.State.Ok shared store).toState (FormalYul.word 4) =
      FormalYul.word x := by
  simp [EvmYul.State.calldataload, EvmYul.Yul.State.toState, hdata,
    selector_lnWadToRay, FormalYul.encodeWords]

private theorem call_cleanup_t_int256_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [v] (.some "cleanup_t_int256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [v]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_cleanup_t_int256]
  simp only [yulFunction_cleanup_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert]

private theorem call_validator_revert_t_int256_direct
    (v : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 60) [v] (.some "validator_revert_t_int256")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, []) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_validator_revert_t_int256]
  simp only [yulFunction_validator_revert_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hcleanup :=
    call_cleanup_t_int256_direct (v := v) (fuel := fuel + 31) (shared := shared)
      (store := Finmap.insert "value" v (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)
  simp [] at hcleanup
  simp +decide [EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    hcleanup]

private theorem call_abi_decode_t_int256_of_calldata
    (x : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_lnWadToRay ++ FormalYul.encodeWords [x]) :
    EvmYul.Yul.call (fuel + 80) [FormalYul.word 4, FormalYul.word 36]
      (.some "abi_decode_t_int256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word x]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_abi_decode_t_int256]
  simp only [yulFunction_abi_decode_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hvalidator :=
    call_validator_revert_t_int256_direct (v := FormalYul.word x) (fuel := fuel + 15)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word x)
        (Finmap.insert "offset" (FormalYul.word 4)
          (Finmap.insert "end" (FormalYul.word 36) (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup)
  simp [FormalYul.word] at hvalidator
  have hload :=
    calldataload_lnWadToRay_arg_of_calldata x shared
      (Finmap.insert "offset" (FormalYul.word 4)
        (Finmap.insert "end" (FormalYul.word 36) (Inhabited.default : EvmYul.Yul.VarStore)))
      hdata
  simp [FormalYul.word] at hload
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hload, hvalidator]

private theorem call_abi_decode_tuple_t_int256_of_calldata
    (x : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_lnWadToRay ++ FormalYul.encodeWords [x]) :
    EvmYul.Yul.call (fuel + 130) [FormalYul.word 4, FormalYul.word 36]
      (.some "abi_decode_tuple_t_int256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word x]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_abi_decode_tuple_t_int256]
  simp only [yulFunction_abi_decode_tuple_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hdecode :=
    call_abi_decode_t_int256_of_calldata (x := x) (fuel := fuel + 43)
      (shared := shared)
      (store := Finmap.insert "offset" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "headStart" (FormalYul.word 4)
          (Finmap.insert "dataEnd" (FormalYul.word 36)
            (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup) (hdata := hdata)
  simp [FormalYul.word] at hdecode
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hdecode]

private theorem call_allocate_unbounded_direct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [] (.some "allocate_unbounded") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok
      ((EvmYul.Yul.State.Ok shared store).setMachineState
        (((EvmYul.Yul.State.Ok shared store).toMachineState.mload (FormalYul.word 64)).2),
        [((EvmYul.Yul.State.Ok shared store).toMachineState.mload (FormalYul.word 64)).1]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_allocate_unbounded]
  simp only [yulFunction_allocate_unbounded,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

private theorem call_abi_encode_t_int256_to_t_int256_fromStack_direct
    (value pos : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 90) [value, pos] (.some "abi_encode_t_int256_to_t_int256_fromStack")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok ((EvmYul.Yul.State.Ok shared store).setMachineState
      ((EvmYul.Yul.State.Ok shared store).toMachineState.mstore pos value), []) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_abi_encode_t_int256_to_t_int256_fromStack]
  simp only [yulFunction_abi_encode_t_int256_to_t_int256_fromStack,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hcleanup :=
    call_cleanup_t_int256_direct (v := value) (fuel := fuel + 64) (shared := shared)
      (store := Finmap.insert "value" value
        (Finmap.insert "pos" pos (Inhabited.default : EvmYul.Yul.VarStore)))
      (hlookup := hlookup)
  simp [] at hcleanup
  simp +decide [EvmYul.Yul.evalCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    hcleanup]

private theorem call_abi_encode_tuple_t_int256_to_t_int256_fromStack_direct
    (headStart value : EvmYul.UInt256) (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 150) [headStart, value]
      (.some "abi_encode_tuple_t_int256__to_t_int256__fromStack")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok ((EvmYul.Yul.State.Ok shared store).setMachineState
      ((EvmYul.Yul.State.Ok shared store).toMachineState.mstore headStart value),
      [headStart + FormalYul.word 32]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions,
    lookup_abi_encode_tuple_t_int256_to_t_int256_fromStack]
  simp only [yulFunction_abi_encode_tuple_t_int256_to_t_int256_fromStack,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hencode :=
    call_abi_encode_t_int256_to_t_int256_fromStack_direct
      (value := value) (pos := headStart + FormalYul.word 0) (fuel := fuel + 55)
      (shared := shared)
      (store := Finmap.insert "tail" (headStart + FormalYul.word 32)
        (Finmap.insert "headStart" headStart
          (Finmap.insert "value0" value (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup)
  simp [FormalYul.word] at hencode
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hencode]

set_option maxHeartbeats 8000000 in
private theorem external_fun_wrap_lnWadToRay_calldata_result
    (x : Nat) (store : EvmYul.Yul.VarStore)
    (hpos : 1 ≤ FormalYul.u256 x) (hpos2 : FormalYul.u256 x < 2 ^ 255) :
    ((match
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_lnWadToRay) (.some yulContract)
        (EvmYul.Yul.State.Ok (lnWadToRaySharedAfterFreePtr x) store)
    with
    | .error (.YulHalt state _) => FormalYul.resultWord (FormalYul.returnOf state)
    | .error .Revert => .error "revert"
    | .error err => .error (reprStr err)
    | .ok (state, _) => FormalYul.resultWord (FormalYul.returnOf state)) :
      Except String Nat) =
      .ok (lnWadToRayBody (FormalYul.u256 x)) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [lnWadToRaySharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_lnWadToRay]
  simp only [yulFunction_external_fun_wrap_lnWadToRay, yulFunction_external_fun_wrap_lnWadToRay_46,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let ret := lnWadToRayBody (FormalYul.u256 x)
  let baseStore :=
    Finmap.insert "ret_0" (FormalYul.word ret)
      (Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let memPos :=
    ((EvmYul.Yul.State.Ok (lnWadToRaySharedAfterFreePtr x) baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { lnWadToRaySharedAfterFreePtr x with
      toMachineState :=
        ((EvmYul.Yul.State.Ok (lnWadToRaySharedAfterFreePtr x) baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_int256_of_calldata (x := x) (fuel := 999854)
      (shared := lnWadToRaySharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := lnWadToRaySharedAfterFreePtr_lookup x)
      (hdata := lnWadToRaySharedAfterFreePtr_calldata x)
  simp [FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_lnWadToRay_direct (x := x) (fuel := 999183)
      (shared := lnWadToRaySharedAfterFreePtr x)
      (store := Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := lnWadToRaySharedAfterFreePtr_lookup x) hpos hpos2
  simp [FormalYul.word, yulName_fun_wrap_lnWadToRay] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999962) (shared := lnWadToRaySharedAfterFreePtr x)
      (store := baseStore) (hlookup := lnWadToRaySharedAfterFreePtr_lookup x)
  simp [FormalYul.word, baseStore] at halloc
  have hencode :=
    call_abi_encode_tuple_t_int256_to_t_int256_fromStack_direct
      (headStart := memPos) (value := FormalYul.word ret) (fuel := 999831)
      (shared := memShared) (store := encStore)
      (hlookup := by simp [memShared, lnWadToRaySharedAfterFreePtr_lookup x])
  simp [FormalYul.word, memShared, encStore, memPos, baseStore, ret] at hencode
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.executionEnv,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.store,
    EvmYul.Yul.State.toMachineState, FormalYul.returnOf,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    hdecode, hwrap, halloc, hencode, ret]
  have hmload :
      ((lnWadToRaySharedAfterFreePtr x).mload (EvmYul.UInt256.ofNat 64)).1 =
        EvmYul.UInt256.ofNat 128 := by
    simpa [FormalYul.word] using lnWadToRaySharedAfterFreePtr_mload64 x
  rw [hmload]
  have hretLen :
      EvmYul.UInt256.ofNat 128 + EvmYul.UInt256.ofNat 32 - EvmYul.UInt256.ofNat 128 =
        FormalYul.word 32 := by decide
  rw [hretLen]
  rw [FormalYul.Preservation.resultWord_evmReturn_mstore_word]
  have hnat :
      (EvmYul.UInt256.ofNat (lnWadToRayBody (FormalYul.u256 x))).toNat =
        lnWadToRayBody (FormalYul.u256 x) := by
    change FormalYul.wordNat (EvmYul.UInt256.ofNat (lnWadToRayBody (FormalYul.u256 x))) =
      lnWadToRayBody (FormalYul.u256 x)
    exact (FormalYul.Preservation.wordNat_ofNat (lnWadToRayBody (FormalYul.u256 x))).trans
      (FormalYul.Preservation.u256_eq_of_lt _ (lnWadToRayBody_lt (u256_lt_word x)))
  rw [hnat]

set_option maxHeartbeats 8000000 in
private theorem external_fun_wrap_lnWadToRay_calldata_halts
    (x : Nat) (store : EvmYul.Yul.VarStore)
    (hpos : 1 ≤ FormalYul.u256 x) (hpos2 : FormalYul.u256 x < 2 ^ 255) :
    ∃ state value,
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_lnWadToRay) (.some yulContract)
        (EvmYul.Yul.State.Ok (lnWadToRaySharedAfterFreePtr x) store) =
        .error (.YulHalt state value) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [lnWadToRaySharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_lnWadToRay]
  simp only [yulFunction_external_fun_wrap_lnWadToRay, yulFunction_external_fun_wrap_lnWadToRay_46,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let ret := lnWadToRayBody (FormalYul.u256 x)
  let baseStore :=
    Finmap.insert "ret_0" (FormalYul.word ret)
      (Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let memPos :=
    ((EvmYul.Yul.State.Ok (lnWadToRaySharedAfterFreePtr x) baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { lnWadToRaySharedAfterFreePtr x with
      toMachineState :=
        ((EvmYul.Yul.State.Ok (lnWadToRaySharedAfterFreePtr x) baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_int256_of_calldata (x := x) (fuel := 999854)
      (shared := lnWadToRaySharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := lnWadToRaySharedAfterFreePtr_lookup x)
      (hdata := lnWadToRaySharedAfterFreePtr_calldata x)
  simp [FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_lnWadToRay_direct (x := x) (fuel := 999183)
      (shared := lnWadToRaySharedAfterFreePtr x)
      (store := Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := lnWadToRaySharedAfterFreePtr_lookup x) hpos hpos2
  simp [FormalYul.word, yulName_fun_wrap_lnWadToRay] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999962) (shared := lnWadToRaySharedAfterFreePtr x)
      (store := baseStore) (hlookup := lnWadToRaySharedAfterFreePtr_lookup x)
  simp [FormalYul.word, baseStore] at halloc
  have hencode :=
    call_abi_encode_tuple_t_int256_to_t_int256_fromStack_direct
      (headStart := memPos) (value := FormalYul.word ret) (fuel := 999831)
      (shared := memShared) (store := encStore)
      (hlookup := by simp [memShared, lnWadToRaySharedAfterFreePtr_lookup x])
  simp [FormalYul.word, memShared, encStore, memPos, baseStore, ret] at hencode
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.executionEnv,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.store,
    EvmYul.Yul.State.toMachineState,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    hdecode, hwrap, halloc, hencode, ret]

private theorem call_shift_right_224_unsigned_direct
    (v : EvmYul.UInt256) (fuel : Nat)
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract)) :
    EvmYul.Yul.call (fuel + 20) [v] (.some "shift_right_224_unsigned")
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store,
      [EvmYul.UInt256.shiftRight v (FormalYul.word 224)]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup,
    Option.getD_some, yulContract_functions, lookup_shift_right_224_unsigned]
  simp only [yulFunction_shift_right_224_unsigned,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  simp +decide [
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word]

private theorem sharedFor_inherited_mstore_mk_eq_lnWadToRaySharedAfterFreePtr (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_lnWadToRay ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_lnWadToRay ++ FormalYul.encodeWords [x])).mstore
          (FormalYul.word 64) (FormalYul.word 128))) =
      lnWadToRaySharedAfterFreePtr x := rfl

private theorem sharedFor_inherited_mstore_mk_eq_lnWadToRaySharedAfterFreePtr_raw (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_lnWadToRay ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_lnWadToRay ++ FormalYul.encodeWords [x])).mstore
          (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128))) =
      lnWadToRaySharedAfterFreePtr x := by
  simpa [FormalYul.word] using sharedFor_inherited_mstore_mk_eq_lnWadToRaySharedAfterFreePtr x

@[simp]
private theorem sharedFor_lnWadToRay_calldata_size (x : Nat) :
    (FormalYul.sharedFor yulContract
      (selector_lnWadToRay ++ FormalYul.encodeWords [x])).executionEnv.calldata.size = 36 := by
  simp [FormalYul.sharedFor, FormalYul.envFor, lnWadToRay_calldata_size]

private theorem lnWadToRay_selector_afterFreePtr (x : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok (lnWadToRaySharedAfterFreePtr x)
          (Inhabited.default : EvmYul.Yul.VarStore)).toState
        (FormalYul.word 0))
      (FormalYul.word 224) =
      FormalYul.word 4010811976 := by
  have hselector :=
    FormalYul.Preservation.shiftRight_calldataload_selector_single_arg_of_calldata
      (shared := lnWadToRaySharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (a := 0xef) (b := 0x10) (c := 0x22) (d := 0x48) (x := x)
      (by simp [selector_lnWadToRay])
  simpa [EvmYul.fromBytesBigEndian, EvmYul.fromBytes', FormalYul.word] using hselector

@[simp]
private theorem lnWadToRay_selector_sharedFor_mk (x : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_lnWadToRay ++ FormalYul.encodeWords [x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_lnWadToRay ++ FormalYul.encodeWords [x])).mstore
                (FormalYul.word 64) (FormalYul.word 128)))
          (Inhabited.default : EvmYul.Yul.VarStore)).toState
        (FormalYul.word 0))
      (FormalYul.word 224) =
      FormalYul.word 4010811976 := by
  rw [sharedFor_inherited_mstore_mk_eq_lnWadToRaySharedAfterFreePtr]
  exact lnWadToRay_selector_afterFreePtr x

@[simp]
private theorem selectSwitchCase_lnWadToRay_sharedFor_mk (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok
            (EvmYul.SharedState.mk
              (FormalYul.sharedFor yulContract
                (selector_lnWadToRay ++ FormalYul.encodeWords [x])).toState
              ((FormalYul.sharedFor yulContract
                (selector_lnWadToRay ++ FormalYul.encodeWords [x])).mstore
                  (FormalYul.word 64) (FormalYul.word 128)))
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (FormalYul.word 0))
        (FormalYul.word 224))
      [(FormalYul.word 835988157,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_lnWad_59") [])]),
        (FormalYul.word 4010811976,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_lnWadToRay_46") [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_lnWadToRay_46") [])] := by
  rw [lnWadToRay_selector_sharedFor_mk]
  rfl

private theorem selectSwitchCase_lnWadToRay_sharedFor_mk_raw (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok
            (EvmYul.SharedState.mk
              (FormalYul.sharedFor yulContract
                (selector_lnWadToRay ++ FormalYul.encodeWords [x])).toState
              ((FormalYul.sharedFor yulContract
                (selector_lnWadToRay ++ FormalYul.encodeWords [x])).mstore
                  (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224))
      [(EvmYul.UInt256.ofNat 835988157,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_lnWad_59") [])]),
        (EvmYul.UInt256.ofNat 4010811976,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_lnWadToRay_46") [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_lnWadToRay_46") [])] := by
  simpa [FormalYul.word] using selectSwitchCase_lnWadToRay_sharedFor_mk x

set_option maxHeartbeats 8000000 in
private theorem external_fun_wrap_lnWadToRay_dispatcher_state_result
    (x : Nat) (hpos : 1 ≤ FormalYul.u256 x) (hpos2 : FormalYul.u256 x < 2 ^ 255) :
    ((match
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_lnWadToRay) (.some yulContract)
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_lnWadToRay ++ FormalYul.encodeWords [x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_lnWadToRay ++ FormalYul.encodeWords [x])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
          (Finmap.insert "selector"
            (EvmYul.UInt256.shiftRight
              (EvmYul.State.calldataload
                (EvmYul.Yul.State.Ok
                  (EvmYul.SharedState.mk
                    (FormalYul.sharedFor yulContract
                      (selector_lnWadToRay ++ FormalYul.encodeWords [x])).toState
                    ((FormalYul.sharedFor yulContract
                      (selector_lnWadToRay ++ FormalYul.encodeWords [x])).mstore
                        (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
                  (Inhabited.default : EvmYul.Yul.VarStore)).toState
                (EvmYul.UInt256.ofNat 0))
              (EvmYul.UInt256.ofNat 224))
            (Inhabited.default : EvmYul.Yul.VarStore)))
    with
    | .error (.YulHalt state _) => FormalYul.resultWord (FormalYul.returnOf state)
    | .error .Revert => .error "revert"
    | .error err => .error (reprStr err)
    | .ok (state, _) => FormalYul.resultWord (FormalYul.returnOf state)) :
      Except String Nat) =
      .ok (lnWadToRayBody (FormalYul.u256 x)) := by
  rw [sharedFor_inherited_mstore_mk_eq_lnWadToRaySharedAfterFreePtr_raw]
  exact external_fun_wrap_lnWadToRay_calldata_result (x := x)
    (store := Finmap.insert "selector"
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok (lnWadToRaySharedAfterFreePtr x)
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224))
      (Inhabited.default : EvmYul.Yul.VarStore)) hpos hpos2

set_option maxHeartbeats 8000000 in
private theorem external_fun_wrap_lnWadToRay_dispatcher_state_halts
    (x : Nat) (hpos : 1 ≤ FormalYul.u256 x) (hpos2 : FormalYul.u256 x < 2 ^ 255) :
    ∃ state value,
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_lnWadToRay) (.some yulContract)
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_lnWadToRay ++ FormalYul.encodeWords [x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_lnWadToRay ++ FormalYul.encodeWords [x])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
          (Finmap.insert "selector"
            (EvmYul.UInt256.shiftRight
              (EvmYul.State.calldataload
                (EvmYul.Yul.State.Ok
                  (EvmYul.SharedState.mk
                    (FormalYul.sharedFor yulContract
                      (selector_lnWadToRay ++ FormalYul.encodeWords [x])).toState
                    ((FormalYul.sharedFor yulContract
                      (selector_lnWadToRay ++ FormalYul.encodeWords [x])).mstore
                        (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
                  (Inhabited.default : EvmYul.Yul.VarStore)).toState
                (EvmYul.UInt256.ofNat 0))
              (EvmYul.UInt256.ofNat 224))
            (Inhabited.default : EvmYul.Yul.VarStore))) =
        .error (.YulHalt state value) := by
  rw [sharedFor_inherited_mstore_mk_eq_lnWadToRaySharedAfterFreePtr_raw]
  exact external_fun_wrap_lnWadToRay_calldata_halts (x := x)
    (store := Finmap.insert "selector"
        (EvmYul.UInt256.shiftRight
          (EvmYul.State.calldataload
            (EvmYul.Yul.State.Ok (lnWadToRaySharedAfterFreePtr x)
              (Inhabited.default : EvmYul.Yul.VarStore)).toState
            (EvmYul.UInt256.ofNat 0))
          (EvmYul.UInt256.ofNat 224))
        (Inhabited.default : EvmYul.Yul.VarStore)) hpos hpos2

set_option maxHeartbeats 8000000 in
theorem run_ln_wad_to_ray_evm_eq_body
    (x : Nat) (hpos : 1 ≤ FormalYul.u256 x) (hpos2 : FormalYul.u256 x < 2 ^ 255) :
    run_ln_wad_to_ray_evm x = .ok (lnWadToRayBody (FormalYul.u256 x)) := by
  obtain ⟨haltState, _haltValue, hhalt⟩ :=
    external_fun_wrap_lnWadToRay_dispatcher_state_halts x hpos hpos2
  have hresult := external_fun_wrap_lnWadToRay_dispatcher_state_result x hpos hpos2
  rw [hhalt] at hresult
  have hReturn :
      FormalYul.Preservation.DispatcherReturn yulContract
        (FormalYul.calldata selector_lnWadToRay [x]) 999998 (FormalYul.returnOf haltState) := by
    apply FormalYul.Preservation.dispatcherReturn_of_exec_halt
      (hdispatcher := yulContract_dispatcher)
    refine ⟨haltState, _haltValue, ?_, rfl⟩
    simp +decide [FormalYul.calldata, FormalYul.stateFor,
      yulDispatcher, EvmYul.Yul.execCall.eq_def,
      EvmYul.Yul.execPrimCall.eq_def,
      EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
      EvmYul.Yul.head', EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
      EvmYul.Yul.State.insert,
      EvmYul.Yul.State.multifill,
      EvmYul.Yul.State.executionEnv,
      EvmYul.Yul.State.toMachineState,
      FormalYul.word,
      call_shift_right_224_unsigned_direct]
    rw [selectSwitchCase_lnWadToRay_sharedFor_mk_raw x]
    simp +decide [hhalt, EvmYul.Yul.exec.eq_def,
      EvmYul.Yul.execCall.eq_def,
      EvmYul.Yul.reverse', EvmYul.Yul.multifill']
  unfold run_ln_wad_to_ray_evm
  exact FormalYul.Preservation.callWord_ok_of_dispatcherReturn_result_1000000
    (contract := yulContract) (selector := selector_lnWadToRay) (args := [x])
    (hReturn := hReturn) (by simpa using hresult)

/-! ## WAD path -/

/-- Shared state after the dispatcher's `mstore(64,128)` free-pointer init, for the
lnWad calldata. -/
private def lnWadSharedAfterFreePtr (x : Nat) : EvmYul.SharedState .Yul :=
  let shared := FormalYul.sharedFor yulContract (selector_lnWad ++ FormalYul.encodeWords [x])
  { shared with toMachineState := shared.toMachineState.mstore (FormalYul.word 64) (FormalYul.word 128) }

@[simp]
private theorem lnWadSharedAfterFreePtr_lookup (x : Nat) :
    (lnWadSharedAfterFreePtr x).accountMap.find?
        (lnWadSharedAfterFreePtr x).executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract) := by
  simp [lnWadSharedAfterFreePtr]

@[simp]
private theorem lnWadSharedAfterFreePtr_calldata (x : Nat) :
    (lnWadSharedAfterFreePtr x).executionEnv.calldata =
      selector_lnWad ++ FormalYul.encodeWords [x] := by
  simp [lnWadSharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp]
private theorem lnWadSharedAfterFreePtr_weiValue (x : Nat) :
    (lnWadSharedAfterFreePtr x).executionEnv.weiValue = ({ val := 0 } : EvmYul.UInt256) := by
  simp [lnWadSharedAfterFreePtr, FormalYul.sharedFor, FormalYul.envFor]

@[simp]
private theorem lnWadSharedAfterFreePtr_mload64 (x : Nat) :
    ((lnWadSharedAfterFreePtr x).mload (FormalYul.word 64)).1 = FormalYul.word 128 :=
  FormalYul.Preservation.sharedFor_mload_freePtr_after_mstore yulContract
    (selector_lnWad ++ FormalYul.encodeWords [x])

@[simp]
private theorem lnWad_calldata_size (x : Nat) :
    (selector_lnWad ++ FormalYul.encodeWords [x]).size = 36 := by
  simp [selector_lnWad, FormalYul.encodeWords,
    FormalYul.bytes, ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
    FormalYul.Preservation.encodeWord_size]

@[simp]
private theorem calldataload_lnWad_arg_of_calldata
    (x : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hdata : shared.executionEnv.calldata = selector_lnWad ++ FormalYul.encodeWords [x]) :
    EvmYul.State.calldataload
      (EvmYul.Yul.State.Ok shared store).toState (FormalYul.word 4) =
      FormalYul.word x := by
  simp [EvmYul.State.calldataload, EvmYul.Yul.State.toState, hdata,
    selector_lnWad, FormalYul.encodeWords]

private theorem call_abi_decode_t_int256_lnWad_of_calldata
    (x : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_lnWad ++ FormalYul.encodeWords [x]) :
    EvmYul.Yul.call (fuel + 80) [FormalYul.word 4, FormalYul.word 36]
      (.some "abi_decode_t_int256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word x]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_abi_decode_t_int256]
  simp only [yulFunction_abi_decode_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hvalidator :=
    call_validator_revert_t_int256_direct (v := FormalYul.word x) (fuel := fuel + 15)
      (shared := shared)
      (store := Finmap.insert "value" (FormalYul.word x)
        (Finmap.insert "offset" (FormalYul.word 4)
          (Finmap.insert "end" (FormalYul.word 36) (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup)
  simp [FormalYul.word] at hvalidator
  have hload :=
    calldataload_lnWad_arg_of_calldata x shared
      (Finmap.insert "offset" (FormalYul.word 4)
        (Finmap.insert "end" (FormalYul.word 36) (Inhabited.default : EvmYul.Yul.VarStore)))
      hdata
  simp [FormalYul.word] at hload
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hload, hvalidator]

private theorem call_abi_decode_tuple_t_int256_lnWad_of_calldata
    (x : Nat) (fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hdata : shared.executionEnv.calldata = selector_lnWad ++ FormalYul.encodeWords [x]) :
    EvmYul.Yul.call (fuel + 130) [FormalYul.word 4, FormalYul.word 36]
      (.some "abi_decode_tuple_t_int256") (.some yulContract)
      (EvmYul.Yul.State.Ok shared store) =
    .ok (EvmYul.Yul.State.Ok shared store, [FormalYul.word x]) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_abi_decode_tuple_t_int256]
  simp only [yulFunction_abi_decode_tuple_t_int256,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hdecode :=
    call_abi_decode_t_int256_lnWad_of_calldata (x := x) (fuel := fuel + 43)
      (shared := shared)
      (store := Finmap.insert "offset" (EvmYul.UInt256.ofNat 0)
        (Finmap.insert "headStart" (FormalYul.word 4)
          (Finmap.insert "dataEnd" (FormalYul.word 36)
            (Inhabited.default : EvmYul.Yul.VarStore))))
      (hlookup := hlookup) (hdata := hdata)
  simp [FormalYul.word] at hdecode
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.reviveJump, EvmYul.Yul.State.overwrite?,
    Finmap.lookup_insert, FormalYul.word, hdecode]

set_option maxHeartbeats 8000000 in
private theorem external_fun_wrap_lnWad_calldata_result
    (x : Nat) (store : EvmYul.Yul.VarStore)
    (hpos : 1 ≤ FormalYul.u256 x) (hpos2 : FormalYul.u256 x < 2 ^ 255) :
    ((match
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_lnWad) (.some yulContract)
        (EvmYul.Yul.State.Ok (lnWadSharedAfterFreePtr x) store)
    with
    | .error (.YulHalt state _) => FormalYul.resultWord (FormalYul.returnOf state)
    | .error .Revert => .error "revert"
    | .error err => .error (reprStr err)
    | .ok (state, _) => FormalYul.resultWord (FormalYul.returnOf state)) :
      Except String Nat) =
      .ok (lnWadBody (FormalYul.u256 x)) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [lnWadSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_lnWad]
  simp only [yulFunction_external_fun_wrap_lnWad, yulFunction_external_fun_wrap_lnWad_59,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let ret := lnWadBody (FormalYul.u256 x)
  let baseStore :=
    Finmap.insert "ret_0" (FormalYul.word ret)
      (Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let memPos :=
    ((EvmYul.Yul.State.Ok (lnWadSharedAfterFreePtr x) baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { lnWadSharedAfterFreePtr x with
      toMachineState :=
        ((EvmYul.Yul.State.Ok (lnWadSharedAfterFreePtr x) baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_int256_lnWad_of_calldata (x := x) (fuel := 999854)
      (shared := lnWadSharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := lnWadSharedAfterFreePtr_lookup x)
      (hdata := lnWadSharedAfterFreePtr_calldata x)
  simp [FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_lnWad_direct (x := x) (fuel := 998883)
      (shared := lnWadSharedAfterFreePtr x)
      (store := Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := lnWadSharedAfterFreePtr_lookup x) hpos hpos2
  simp [FormalYul.word, yulName_fun_wrap_lnWad] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999962) (shared := lnWadSharedAfterFreePtr x)
      (store := baseStore) (hlookup := lnWadSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, baseStore] at halloc
  have hencode :=
    call_abi_encode_tuple_t_int256_to_t_int256_fromStack_direct
      (headStart := memPos) (value := FormalYul.word ret) (fuel := 999831)
      (shared := memShared) (store := encStore)
      (hlookup := by simp [memShared, lnWadSharedAfterFreePtr_lookup x])
  simp [FormalYul.word, memShared, encStore, memPos, baseStore, ret] at hencode
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.executionEnv,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.store,
    EvmYul.Yul.State.toMachineState, FormalYul.returnOf,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    hdecode, hwrap, halloc, hencode, ret]
  have hmload :
      ((lnWadSharedAfterFreePtr x).mload (EvmYul.UInt256.ofNat 64)).1 =
        EvmYul.UInt256.ofNat 128 := by
    simpa [FormalYul.word] using lnWadSharedAfterFreePtr_mload64 x
  rw [hmload]
  have hretLen :
      EvmYul.UInt256.ofNat 128 + EvmYul.UInt256.ofNat 32 - EvmYul.UInt256.ofNat 128 =
        FormalYul.word 32 := by decide
  rw [hretLen]
  rw [FormalYul.Preservation.resultWord_evmReturn_mstore_word]
  have hnat :
      (EvmYul.UInt256.ofNat (lnWadBody (FormalYul.u256 x))).toNat =
        lnWadBody (FormalYul.u256 x) := by
    change FormalYul.wordNat (EvmYul.UInt256.ofNat (lnWadBody (FormalYul.u256 x))) =
      lnWadBody (FormalYul.u256 x)
    exact (FormalYul.Preservation.wordNat_ofNat (lnWadBody (FormalYul.u256 x))).trans
      (FormalYul.Preservation.u256_eq_of_lt _ (to_wad_lt (u256_lt_word x)))
  rw [hnat]

set_option maxHeartbeats 8000000 in
private theorem external_fun_wrap_lnWad_calldata_halts
    (x : Nat) (store : EvmYul.Yul.VarStore)
    (hpos : 1 ≤ FormalYul.u256 x) (hpos2 : FormalYul.u256 x < 2 ^ 255) :
    ∃ state value,
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_lnWad) (.some yulContract)
        (EvmYul.Yul.State.Ok (lnWadSharedAfterFreePtr x) store) =
        .error (.YulHalt state value) := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [lnWadSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_lnWad]
  simp only [yulFunction_external_fun_wrap_lnWad, yulFunction_external_fun_wrap_lnWad_59,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  let ret := lnWadBody (FormalYul.u256 x)
  let baseStore :=
    Finmap.insert "ret_0" (FormalYul.word ret)
      (Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
  let memPos :=
    ((EvmYul.Yul.State.Ok (lnWadSharedAfterFreePtr x) baseStore).toMachineState.mload
      (FormalYul.word 64)).1
  let memShared :=
    { lnWadSharedAfterFreePtr x with
      toMachineState :=
        ((EvmYul.Yul.State.Ok (lnWadSharedAfterFreePtr x) baseStore).toMachineState.mload
          (FormalYul.word 64)).2 }
  let encStore := Finmap.insert "memPos" memPos baseStore
  have hdecode :=
    call_abi_decode_tuple_t_int256_lnWad_of_calldata (x := x) (fuel := 999854)
      (shared := lnWadSharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := lnWadSharedAfterFreePtr_lookup x)
      (hdata := lnWadSharedAfterFreePtr_calldata x)
  simp [FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_lnWad_direct (x := x) (fuel := 998883)
      (shared := lnWadSharedAfterFreePtr x)
      (store := Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := lnWadSharedAfterFreePtr_lookup x) hpos hpos2
  simp [FormalYul.word, yulName_fun_wrap_lnWad] at hwrap
  have halloc :=
    call_allocate_unbounded_direct (fuel := 999962) (shared := lnWadSharedAfterFreePtr x)
      (store := baseStore) (hlookup := lnWadSharedAfterFreePtr_lookup x)
  simp [FormalYul.word, baseStore] at halloc
  have hencode :=
    call_abi_encode_tuple_t_int256_to_t_int256_fromStack_direct
      (headStart := memPos) (value := FormalYul.word ret) (fuel := 999831)
      (shared := memShared) (store := encStore)
      (hlookup := by simp [memShared, lnWadSharedAfterFreePtr_lookup x])
  simp [FormalYul.word, memShared, encStore, memPos, baseStore, ret] at hencode
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.execPrimCall.eq_def, EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.executionEnv,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.store,
    EvmYul.Yul.State.toMachineState,
    Finmap.lookup_insert, Finmap.lookup_insert_of_ne,
    hdecode, hwrap, halloc, hencode, ret]

private theorem sharedFor_inherited_mstore_mk_eq_lnWadSharedAfterFreePtr (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_lnWad ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_lnWad ++ FormalYul.encodeWords [x])).mstore
          (FormalYul.word 64) (FormalYul.word 128))) =
      lnWadSharedAfterFreePtr x := rfl

private theorem sharedFor_inherited_mstore_mk_eq_lnWadSharedAfterFreePtr_raw (x : Nat) :
    (EvmYul.SharedState.mk
        (FormalYul.sharedFor yulContract (selector_lnWad ++ FormalYul.encodeWords [x])).toState
        ((FormalYul.sharedFor yulContract (selector_lnWad ++ FormalYul.encodeWords [x])).mstore
          (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128))) =
      lnWadSharedAfterFreePtr x := by
  simpa [FormalYul.word] using sharedFor_inherited_mstore_mk_eq_lnWadSharedAfterFreePtr x

@[simp]
private theorem sharedFor_lnWad_calldata_size (x : Nat) :
    (FormalYul.sharedFor yulContract
      (selector_lnWad ++ FormalYul.encodeWords [x])).executionEnv.calldata.size = 36 := by
  simp [FormalYul.sharedFor, FormalYul.envFor, lnWad_calldata_size]

private theorem lnWad_selector_afterFreePtr (x : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok (lnWadSharedAfterFreePtr x)
          (Inhabited.default : EvmYul.Yul.VarStore)).toState
        (FormalYul.word 0))
      (FormalYul.word 224) =
      FormalYul.word 835988157 := by
  have hselector :=
    FormalYul.Preservation.shiftRight_calldataload_selector_single_arg_of_calldata
      (shared := lnWadSharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (a := 0x31) (b := 0xd4) (c := 0x2a) (d := 0xbd) (x := x)
      (by simp [selector_lnWad])
  simpa [EvmYul.fromBytesBigEndian, EvmYul.fromBytes', FormalYul.word] using hselector

@[simp]
private theorem lnWad_selector_sharedFor_mk (x : Nat) :
    EvmYul.UInt256.shiftRight
      (EvmYul.State.calldataload
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_lnWad ++ FormalYul.encodeWords [x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_lnWad ++ FormalYul.encodeWords [x])).mstore
                (FormalYul.word 64) (FormalYul.word 128)))
          (Inhabited.default : EvmYul.Yul.VarStore)).toState
        (FormalYul.word 0))
      (FormalYul.word 224) =
      FormalYul.word 835988157 := by
  rw [sharedFor_inherited_mstore_mk_eq_lnWadSharedAfterFreePtr]
  exact lnWad_selector_afterFreePtr x

@[simp]
private theorem selectSwitchCase_lnWad_sharedFor_mk (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok
            (EvmYul.SharedState.mk
              (FormalYul.sharedFor yulContract
                (selector_lnWad ++ FormalYul.encodeWords [x])).toState
              ((FormalYul.sharedFor yulContract
                (selector_lnWad ++ FormalYul.encodeWords [x])).mstore
                  (FormalYul.word 64) (FormalYul.word 128)))
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (FormalYul.word 0))
        (FormalYul.word 224))
      [(FormalYul.word 835988157,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_lnWad_59") [])]),
        (FormalYul.word 4010811976,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_lnWadToRay_46") [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_lnWad_59") [])] := by
  rw [lnWad_selector_sharedFor_mk]
  rfl

private theorem selectSwitchCase_lnWad_sharedFor_mk_raw (x : Nat) :
    EvmYul.Yul.selectSwitchCase
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok
            (EvmYul.SharedState.mk
              (FormalYul.sharedFor yulContract
                (selector_lnWad ++ FormalYul.encodeWords [x])).toState
              ((FormalYul.sharedFor yulContract
                (selector_lnWad ++ FormalYul.encodeWords [x])).mstore
                  (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224))
      [(EvmYul.UInt256.ofNat 835988157,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_lnWad_59") [])]),
        (EvmYul.UInt256.ofNat 4010811976,
          [EvmYul.Yul.Ast.Stmt.ExprStmtCall
            (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_lnWadToRay_46") [])])] =
      some
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (Sum.inr "external_fun_wrap_lnWad_59") [])] := by
  simpa [FormalYul.word] using selectSwitchCase_lnWad_sharedFor_mk x

set_option maxHeartbeats 8000000 in
private theorem external_fun_wrap_lnWad_dispatcher_state_result
    (x : Nat) (hpos : 1 ≤ FormalYul.u256 x) (hpos2 : FormalYul.u256 x < 2 ^ 255) :
    ((match
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_lnWad) (.some yulContract)
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_lnWad ++ FormalYul.encodeWords [x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_lnWad ++ FormalYul.encodeWords [x])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
          (Finmap.insert "selector"
            (EvmYul.UInt256.shiftRight
              (EvmYul.State.calldataload
                (EvmYul.Yul.State.Ok
                  (EvmYul.SharedState.mk
                    (FormalYul.sharedFor yulContract
                      (selector_lnWad ++ FormalYul.encodeWords [x])).toState
                    ((FormalYul.sharedFor yulContract
                      (selector_lnWad ++ FormalYul.encodeWords [x])).mstore
                        (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
                  (Inhabited.default : EvmYul.Yul.VarStore)).toState
                (EvmYul.UInt256.ofNat 0))
              (EvmYul.UInt256.ofNat 224))
            (Inhabited.default : EvmYul.Yul.VarStore)))
    with
    | .error (.YulHalt state _) => FormalYul.resultWord (FormalYul.returnOf state)
    | .error .Revert => .error "revert"
    | .error err => .error (reprStr err)
    | .ok (state, _) => FormalYul.resultWord (FormalYul.returnOf state)) :
      Except String Nat) =
      .ok (lnWadBody (FormalYul.u256 x)) := by
  rw [sharedFor_inherited_mstore_mk_eq_lnWadSharedAfterFreePtr_raw]
  exact external_fun_wrap_lnWad_calldata_result (x := x)
    (store := Finmap.insert "selector"
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok (lnWadSharedAfterFreePtr x)
            (Inhabited.default : EvmYul.Yul.VarStore)).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224))
      (Inhabited.default : EvmYul.Yul.VarStore)) hpos hpos2

set_option maxHeartbeats 8000000 in
private theorem external_fun_wrap_lnWad_dispatcher_state_halts
    (x : Nat) (hpos : 1 ≤ FormalYul.u256 x) (hpos2 : FormalYul.u256 x < 2 ^ 255) :
    ∃ state value,
      EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_lnWad) (.some yulContract)
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_lnWad ++ FormalYul.encodeWords [x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_lnWad ++ FormalYul.encodeWords [x])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
          (Finmap.insert "selector"
            (EvmYul.UInt256.shiftRight
              (EvmYul.State.calldataload
                (EvmYul.Yul.State.Ok
                  (EvmYul.SharedState.mk
                    (FormalYul.sharedFor yulContract
                      (selector_lnWad ++ FormalYul.encodeWords [x])).toState
                    ((FormalYul.sharedFor yulContract
                      (selector_lnWad ++ FormalYul.encodeWords [x])).mstore
                        (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
                  (Inhabited.default : EvmYul.Yul.VarStore)).toState
                (EvmYul.UInt256.ofNat 0))
              (EvmYul.UInt256.ofNat 224))
            (Inhabited.default : EvmYul.Yul.VarStore))) =
        .error (.YulHalt state value) := by
  rw [sharedFor_inherited_mstore_mk_eq_lnWadSharedAfterFreePtr_raw]
  exact external_fun_wrap_lnWad_calldata_halts (x := x)
    (store := Finmap.insert "selector"
        (EvmYul.UInt256.shiftRight
          (EvmYul.State.calldataload
            (EvmYul.Yul.State.Ok (lnWadSharedAfterFreePtr x)
              (Inhabited.default : EvmYul.Yul.VarStore)).toState
            (EvmYul.UInt256.ofNat 0))
          (EvmYul.UInt256.ofNat 224))
        (Inhabited.default : EvmYul.Yul.VarStore)) hpos hpos2

set_option maxHeartbeats 8000000 in
theorem run_ln_wad_evm_eq_body
    (x : Nat) (hpos : 1 ≤ FormalYul.u256 x) (hpos2 : FormalYul.u256 x < 2 ^ 255) :
    run_ln_wad_evm x = .ok (lnWadBody (FormalYul.u256 x)) := by
  obtain ⟨haltState, _haltValue, hhalt⟩ :=
    external_fun_wrap_lnWad_dispatcher_state_halts x hpos hpos2
  have hresult := external_fun_wrap_lnWad_dispatcher_state_result x hpos hpos2
  rw [hhalt] at hresult
  have hReturn :
      FormalYul.Preservation.DispatcherReturn yulContract
        (FormalYul.calldata selector_lnWad [x]) 999998 (FormalYul.returnOf haltState) := by
    apply FormalYul.Preservation.dispatcherReturn_of_exec_halt
      (hdispatcher := yulContract_dispatcher)
    refine ⟨haltState, _haltValue, ?_, rfl⟩
    simp +decide [FormalYul.calldata, FormalYul.stateFor,
      yulDispatcher, EvmYul.Yul.execCall.eq_def,
      EvmYul.Yul.execPrimCall.eq_def,
      EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
      EvmYul.Yul.head', EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
      EvmYul.Yul.State.insert,
      EvmYul.Yul.State.multifill,
      EvmYul.Yul.State.executionEnv,
      EvmYul.Yul.State.toMachineState,
      FormalYul.word,
      call_shift_right_224_unsigned_direct]
    rw [selectSwitchCase_lnWad_sharedFor_mk_raw x]
    simp +decide [hhalt, EvmYul.Yul.exec.eq_def,
      EvmYul.Yul.execCall.eq_def,
      EvmYul.Yul.reverse', EvmYul.Yul.multifill']
  unfold run_ln_wad_evm
  exact FormalYul.Preservation.callWord_ok_of_dispatcherReturn_result_1000000
    (contract := yulContract) (selector := selector_lnWad) (args := [x])
    (hReturn := hReturn) (by simpa using hresult)

/-! ## Revert path (nonpositive input) -/

set_option maxHeartbeats 8000000 in
theorem call_fun_wrap_lnWadToRay_revert_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hnonpos : int256 (FormalYul.u256 x) ≤ 0) :
    EvmYul.Yul.call (fuel + 800) [FormalYul.word x] (.some yulName_fun_wrap_lnWadToRay)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .error EvmYul.Yul.Exception.Revert := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_wrap_lnWadToRay]
  simp only [yulFunction_fun_wrap_lnWadToRay, yulFunction_fun_wrap_lnWadToRay_46,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hfuel : fuel + 791 = (fuel + 191) + 600 := by omega
  have hCall := call_fun_lnWadToRay_revert_direct (x := x) (fuel := fuel + 191) (shared := shared)
    (store := Finmap.insert "expr_42" (EvmYul.UInt256.ofNat x)
      (Finmap.insert "_4" (EvmYul.UInt256.ofNat x)
        (Finmap.insert "expr_40_address" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "var__38" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "zero_t_int256_3" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "var_x_35" (EvmYul.UInt256.ofNat x)
                (Inhabited.default : EvmYul.Yul.VarStore)))))))
    (hlookup := hlookup) hnonpos
  simp only [FormalYul.word, yulName_fun_lnWadToRay] at hCall
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.setStore,
    FormalYul.word, hfuel, hCall,
    call_zero_value_for_split_t_int256_direct (fuel := fuel) (extra := 776)
      (shared := shared)
      (store := Finmap.insert "var_x_35" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]

-- `call_fun_lnWad_revert_direct`: the wad body reverts (it calls
-- `fun_lnWadToRay_11`, which reverts for nonpositive input before the sdiv tail).
set_option maxHeartbeats 8000000 in
theorem call_fun_lnWad_revert_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hnonpos : int256 (FormalYul.u256 x) ≤ 0) :
    EvmYul.Yul.call (fuel + 900) [FormalYul.word x] (.some yulName_fun_lnWad)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .error EvmYul.Yul.Exception.Revert := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_lnWad]
  simp only [yulFunction_fun_lnWad, yulFunction_fun_lnWad_27,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hfuel : fuel + 892 = (fuel + 292) + 600 := by omega
  have hCall := call_fun_lnWadToRay_revert_direct (x := x) (fuel := fuel + 292) (shared := shared)
    (store := Finmap.insert "expr_21" (EvmYul.UInt256.ofNat x)
      (Finmap.insert "_6" (EvmYul.UInt256.ofNat x)
        (Finmap.insert "var_r_17" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "zero_t_int256_5" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "var_x_14" (EvmYul.UInt256.ofNat x)
              (Inhabited.default : EvmYul.Yul.VarStore))))))
    (hlookup := hlookup) hnonpos
  simp only [FormalYul.word, yulName_fun_lnWadToRay] at hCall
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.setStore,
    FormalYul.word, hfuel, hCall,
    call_zero_value_for_split_t_int256_direct (fuel := fuel) (extra := 876)
      (shared := shared)
      (store := Finmap.insert "var_x_14" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]

set_option maxHeartbeats 8000000 in
theorem call_fun_wrap_lnWad_revert_direct
    (x fuel : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hlookup : shared.accountMap.find? shared.executionEnv.codeOwner =
      some (FormalYul.accountFor yulContract))
    (hnonpos : int256 (FormalYul.u256 x) ≤ 0) :
    EvmYul.Yul.call (fuel + 1100) [FormalYul.word x] (.some yulName_fun_wrap_lnWad)
      (.some yulContract) (EvmYul.Yul.State.Ok shared store) =
    .error EvmYul.Yul.Exception.Revert := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [hlookup, Option.getD_some, yulContract_functions, lookup_fun_wrap_lnWad]
  simp only [yulFunction_fun_wrap_lnWad, yulFunction_fun_wrap_lnWad_59,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hfuel : fuel + 1091 = (fuel + 191) + 900 := by omega
  have hCall := call_fun_lnWad_revert_direct (x := x) (fuel := fuel + 191) (shared := shared)
    (store := Finmap.insert "expr_55" (EvmYul.UInt256.ofNat x)
      (Finmap.insert "_2" (EvmYul.UInt256.ofNat x)
        (Finmap.insert "expr_53_address" (EvmYul.UInt256.ofNat 0)
          (Finmap.insert "var__51" (EvmYul.UInt256.ofNat 0)
            (Finmap.insert "zero_t_int256_1" (EvmYul.UInt256.ofNat 0)
              (Finmap.insert "var_x_48" (EvmYul.UInt256.ofNat x)
                (Inhabited.default : EvmYul.Yul.VarStore)))))))
    (hlookup := hlookup) hnonpos
  simp only [FormalYul.word, yulName_fun_lnWad] at hCall
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.setStore,
    FormalYul.word, hfuel, hCall,
    call_zero_value_for_split_t_int256_direct (fuel := fuel) (extra := 1076)
      (shared := shared)
      (store := Finmap.insert "var_x_48" (EvmYul.UInt256.ofNat x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := hlookup)]

set_option maxHeartbeats 8000000 in
theorem external_fun_wrap_lnWadToRay_calldata_revert
    (x : Nat) (store : EvmYul.Yul.VarStore) (hnonpos : int256 (FormalYul.u256 x) ≤ 0) :
    EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_lnWadToRay) (.some yulContract)
        (EvmYul.Yul.State.Ok (lnWadToRaySharedAfterFreePtr x) store) =
      .error EvmYul.Yul.Exception.Revert := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [lnWadToRaySharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_lnWadToRay]
  simp only [yulFunction_external_fun_wrap_lnWadToRay, yulFunction_external_fun_wrap_lnWadToRay_46,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hdecode :=
    call_abi_decode_tuple_t_int256_of_calldata (x := x) (fuel := 999854)
      (shared := lnWadToRaySharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := lnWadToRaySharedAfterFreePtr_lookup x)
      (hdata := lnWadToRaySharedAfterFreePtr_calldata x)
  simp [FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_lnWadToRay_revert_direct (x := x) (fuel := 999183)
      (shared := lnWadToRaySharedAfterFreePtr x)
      (store := Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := lnWadToRaySharedAfterFreePtr_lookup x) hnonpos
  simp [FormalYul.word, yulName_fun_wrap_lnWadToRay] at hwrap
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.executionEnv,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.store,
    Finmap.lookup_insert,
    hdecode, hwrap]

set_option maxHeartbeats 8000000 in
theorem external_fun_wrap_lnWad_calldata_revert
    (x : Nat) (store : EvmYul.Yul.VarStore) (hnonpos : int256 (FormalYul.u256 x) ≤ 0) :
    EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_lnWad) (.some yulContract)
        (EvmYul.Yul.State.Ok (lnWadSharedAfterFreePtr x) store) =
      .error EvmYul.Yul.Exception.Revert := by
  rw [EvmYul.Yul.call.eq_def]
  simp only [lnWadSharedAfterFreePtr_lookup, Option.getD_some, yulContract_functions,
    lookup_external_fun_wrap_lnWad]
  simp only [yulFunction_external_fun_wrap_lnWad, yulFunction_external_fun_wrap_lnWad_59,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def,
    EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk]
  have hdecode :=
    call_abi_decode_tuple_t_int256_lnWad_of_calldata (x := x) (fuel := 999854)
      (shared := lnWadSharedAfterFreePtr x)
      (store := (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := lnWadSharedAfterFreePtr_lookup x)
      (hdata := lnWadSharedAfterFreePtr_calldata x)
  simp [FormalYul.word] at hdecode
  have hwrap :=
    call_fun_wrap_lnWad_revert_direct (x := x) (fuel := 998883)
      (shared := lnWadSharedAfterFreePtr x)
      (store := Finmap.insert "param_0" (FormalYul.word x)
        (Inhabited.default : EvmYul.Yul.VarStore))
      (hlookup := lnWadSharedAfterFreePtr_lookup x) hnonpos
  simp [FormalYul.word, yulName_fun_wrap_lnWad] at hwrap
  simp +decide [EvmYul.Yul.execCall.eq_def,
    EvmYul.Yul.evalPrimCall.eq_def,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.evalTail.eq_def,
    EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.setStore,
    EvmYul.Yul.State.executionEnv,
    GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.store,
    Finmap.lookup_insert,
    hdecode, hwrap]

set_option maxHeartbeats 8000000 in
theorem external_fun_wrap_lnWadToRay_dispatcher_state_revert
    (x : Nat) (hnonpos : int256 (FormalYul.u256 x) ≤ 0) :
    EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_lnWadToRay) (.some yulContract)
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_lnWadToRay ++ FormalYul.encodeWords [x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_lnWadToRay ++ FormalYul.encodeWords [x])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
          (Finmap.insert "selector"
            (EvmYul.UInt256.shiftRight
              (EvmYul.State.calldataload
                (EvmYul.Yul.State.Ok
                  (EvmYul.SharedState.mk
                    (FormalYul.sharedFor yulContract
                      (selector_lnWadToRay ++ FormalYul.encodeWords [x])).toState
                    ((FormalYul.sharedFor yulContract
                      (selector_lnWadToRay ++ FormalYul.encodeWords [x])).mstore
                        (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
                  (Inhabited.default : EvmYul.Yul.VarStore)).toState
                (EvmYul.UInt256.ofNat 0))
              (EvmYul.UInt256.ofNat 224))
            (Inhabited.default : EvmYul.Yul.VarStore))) =
        .error EvmYul.Yul.Exception.Revert := by
  rw [sharedFor_inherited_mstore_mk_eq_lnWadToRaySharedAfterFreePtr_raw]
  exact external_fun_wrap_lnWadToRay_calldata_revert (x := x)
    (store := Finmap.insert "selector"
        (EvmYul.UInt256.shiftRight
          (EvmYul.State.calldataload
            (EvmYul.Yul.State.Ok (lnWadToRaySharedAfterFreePtr x)
              (Inhabited.default : EvmYul.Yul.VarStore)).toState
            (EvmYul.UInt256.ofNat 0))
          (EvmYul.UInt256.ofNat 224))
        (Inhabited.default : EvmYul.Yul.VarStore)) hnonpos

set_option maxHeartbeats 8000000 in
theorem external_fun_wrap_lnWad_dispatcher_state_revert
    (x : Nat) (hnonpos : int256 (FormalYul.u256 x) ≤ 0) :
    EvmYul.Yul.call 999989 [] (.some yulName_external_fun_wrap_lnWad) (.some yulContract)
        (EvmYul.Yul.State.Ok
          (EvmYul.SharedState.mk
            (FormalYul.sharedFor yulContract
              (selector_lnWad ++ FormalYul.encodeWords [x])).toState
            ((FormalYul.sharedFor yulContract
              (selector_lnWad ++ FormalYul.encodeWords [x])).mstore
                (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
          (Finmap.insert "selector"
            (EvmYul.UInt256.shiftRight
              (EvmYul.State.calldataload
                (EvmYul.Yul.State.Ok
                  (EvmYul.SharedState.mk
                    (FormalYul.sharedFor yulContract
                      (selector_lnWad ++ FormalYul.encodeWords [x])).toState
                    ((FormalYul.sharedFor yulContract
                      (selector_lnWad ++ FormalYul.encodeWords [x])).mstore
                        (EvmYul.UInt256.ofNat 64) (EvmYul.UInt256.ofNat 128)))
                  (Inhabited.default : EvmYul.Yul.VarStore)).toState
                (EvmYul.UInt256.ofNat 0))
              (EvmYul.UInt256.ofNat 224))
            (Inhabited.default : EvmYul.Yul.VarStore))) =
        .error EvmYul.Yul.Exception.Revert := by
  rw [sharedFor_inherited_mstore_mk_eq_lnWadSharedAfterFreePtr_raw]
  exact external_fun_wrap_lnWad_calldata_revert (x := x)
    (store := Finmap.insert "selector"
        (EvmYul.UInt256.shiftRight
          (EvmYul.State.calldataload
            (EvmYul.Yul.State.Ok (lnWadSharedAfterFreePtr x)
              (Inhabited.default : EvmYul.Yul.VarStore)).toState
            (EvmYul.UInt256.ofNat 0))
          (EvmYul.UInt256.ofNat 224))
        (Inhabited.default : EvmYul.Yul.VarStore)) hnonpos

/-- Revert-analogue of `Preservation.runContract_ok_of_dispatcherReturn`: if the
bare dispatcher `exec` on `stateFor` reverts, the wrapped `runContract` returns
`.error "revert"`. The state-normalization chain mirrors that lemma; only the
result leaf differs. -/
private theorem runContract_revert_of_exec_revert
    {contract : YulContract} {input : ByteArray} {execFuel : Nat}
    (h : EvmYul.Yul.exec execFuel contract.dispatcher (.some contract)
          (stateFor contract input) = .error EvmYul.Yul.Exception.Revert) :
    runContract contract input (Nat.succ (Nat.succ execFuel)) = .error "revert" := by
  unfold runContract
  rw [EvmYul.Yul.callDispatcher.eq_def]
  simp only [stateFor, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.executionEnv, sharedFor, envFor, accountMapFor, accountFor,
    EvmYul.Yul.State.multifill, EvmYul.Yul.State.setStore, List.zip_nil_left, List.foldr_nil,
    FormalYul.Preservation.functionDefinition_params_def,
    FormalYul.Preservation.functionDefinition_rets_def,
    FormalYul.Preservation.functionDefinition_body_def]
  rw [EvmYul.Yul.exec.eq_def]
  simp only
  have hdisp' :
      EvmYul.Yul.exec execFuel contract.dispatcher (.some contract)
        (EvmYul.Yul.State.Ok
          { (Inhabited.default : EvmYul.SharedState .Yul) with
            accountMap := accountMapFor contract
            executionEnv := envFor contract input
            gasAvailable := .ofNat 1000000000 }
          (Inhabited.default : EvmYul.Yul.VarStore)) =
        .error EvmYul.Yul.Exception.Revert := by
    simpa [stateFor, sharedFor] using h
  have hdisp'' :
      EvmYul.Yul.exec execFuel contract.dispatcher (.some contract)
        (EvmYul.Yul.State.Ok
          { accountMap := accountMapFor contract,
            σ₀ := (Inhabited.default : EvmYul.SharedState .Yul).σ₀,
            totalGasUsedInBlock := (Inhabited.default : EvmYul.SharedState .Yul).totalGasUsedInBlock,
            transactionReceipts := (Inhabited.default : EvmYul.SharedState .Yul).transactionReceipts,
            substate := (Inhabited.default : EvmYul.SharedState .Yul).substate,
            executionEnv := envFor contract input,
            blocks := (Inhabited.default : EvmYul.SharedState .Yul).blocks,
            genesisBlockHeader := (Inhabited.default : EvmYul.SharedState .Yul).genesisBlockHeader,
            createdAccounts := (Inhabited.default : EvmYul.SharedState .Yul).createdAccounts,
            gasAvailable := EvmYul.UInt256.ofNat 1000000000,
            activeWords := (Inhabited.default : EvmYul.SharedState .Yul).activeWords,
            memory := (Inhabited.default : EvmYul.SharedState .Yul).memory,
            returnData := (Inhabited.default : EvmYul.SharedState .Yul).returnData,
            H_return := (Inhabited.default : EvmYul.SharedState .Yul).H_return }
          (Inhabited.default : EvmYul.Yul.VarStore)) =
        .error EvmYul.Yul.Exception.Revert := by
    simpa using hdisp'
  have hdisp''' :
      EvmYul.Yul.exec execFuel contract.dispatcher (.some contract)
        (EvmYul.Yul.State.Ok
          { accountMap := Batteries.RBMap.insert ∅ contractOwner
              { (Inhabited.default : EvmYul.Account .Yul) with code := contract },
            σ₀ := (Inhabited.default : EvmYul.SharedState .Yul).σ₀,
            totalGasUsedInBlock := (Inhabited.default : EvmYul.SharedState .Yul).totalGasUsedInBlock,
            transactionReceipts := (Inhabited.default : EvmYul.SharedState .Yul).transactionReceipts,
            substate := (Inhabited.default : EvmYul.SharedState .Yul).substate,
            executionEnv := { (Inhabited.default : EvmYul.ExecutionEnv .Yul) with
              calldata := input
              code := contract
              codeOwner := contractOwner
              weiValue := ⟨0⟩
              perm := true },
            blocks := (Inhabited.default : EvmYul.SharedState .Yul).blocks,
            genesisBlockHeader := (Inhabited.default : EvmYul.SharedState .Yul).genesisBlockHeader,
            createdAccounts := (Inhabited.default : EvmYul.SharedState .Yul).createdAccounts,
            gasAvailable := EvmYul.UInt256.ofNat 1000000000,
            activeWords := (Inhabited.default : EvmYul.SharedState .Yul).activeWords,
            memory := (Inhabited.default : EvmYul.SharedState .Yul).memory,
            returnData := (Inhabited.default : EvmYul.SharedState .Yul).returnData,
            H_return := (Inhabited.default : EvmYul.SharedState .Yul).H_return }
          (Inhabited.default : EvmYul.Yul.VarStore)) =
        .error EvmYul.Yul.Exception.Revert := by
    simpa [accountMapFor, accountFor, envFor] using hdisp''
  rw [hdisp''']

set_option maxHeartbeats 8000000 in
theorem run_ln_wad_to_ray_evm_revert (x : Nat) (hnonpos : int256 (FormalYul.u256 x) ≤ 0) :
    run_ln_wad_to_ray_evm x = .error "revert" := by
  have hexec :
      EvmYul.Yul.exec 999998 yulContract.dispatcher (.some yulContract)
        (stateFor yulContract (FormalYul.calldata selector_lnWadToRay [x])) =
        .error EvmYul.Yul.Exception.Revert := by
    rw [yulContract_dispatcher]
    simp +decide [FormalYul.calldata, stateFor, yulDispatcher,
      EvmYul.Yul.execCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
      EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
      EvmYul.Yul.head', EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
      EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
      EvmYul.Yul.State.executionEnv, EvmYul.Yul.State.toMachineState,
      FormalYul.word, call_shift_right_224_unsigned_direct]
    rw [selectSwitchCase_lnWadToRay_sharedFor_mk_raw x]
    simp +decide [external_fun_wrap_lnWadToRay_dispatcher_state_revert x hnonpos,
      EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def,
      EvmYul.Yul.reverse', EvmYul.Yul.multifill']
  have hrun :
      runContract yulContract (FormalYul.calldata selector_lnWadToRay [x]) 1000000 =
        .error "revert" :=
    runContract_revert_of_exec_revert hexec
  unfold run_ln_wad_to_ray_evm FormalYul.callWord FormalYul.call
  rw [hrun]
  rfl

set_option maxHeartbeats 8000000 in
theorem run_ln_wad_evm_revert (x : Nat) (hnonpos : int256 (FormalYul.u256 x) ≤ 0) :
    run_ln_wad_evm x = .error "revert" := by
  have hexec :
      EvmYul.Yul.exec 999998 yulContract.dispatcher (.some yulContract)
        (stateFor yulContract (FormalYul.calldata selector_lnWad [x])) =
        .error EvmYul.Yul.Exception.Revert := by
    rw [yulContract_dispatcher]
    simp +decide [FormalYul.calldata, stateFor, yulDispatcher,
      EvmYul.Yul.execCall.eq_def, EvmYul.Yul.execPrimCall.eq_def,
      EvmYul.Yul.evalPrimCall.eq_def, EvmYul.Yul.reverse', EvmYul.Yul.cons',
      EvmYul.Yul.head', EvmYul.Yul.multifill', EvmYul.Yul.evalTail.eq_def,
      EvmYul.Yul.State.insert, EvmYul.Yul.State.multifill,
      EvmYul.Yul.State.executionEnv, EvmYul.Yul.State.toMachineState,
      FormalYul.word, call_shift_right_224_unsigned_direct]
    rw [selectSwitchCase_lnWad_sharedFor_mk_raw x]
    simp +decide [external_fun_wrap_lnWad_dispatcher_state_revert x hnonpos,
      EvmYul.Yul.exec.eq_def, EvmYul.Yul.execCall.eq_def,
      EvmYul.Yul.reverse', EvmYul.Yul.multifill']
  have hrun :
      runContract yulContract (FormalYul.calldata selector_lnWad [x]) 1000000 =
        .error "revert" :=
    runContract_revert_of_exec_revert hexec
  unfold run_ln_wad_evm FormalYul.callWord FormalYul.call
  rw [hrun]
  rfl

end LnYul
