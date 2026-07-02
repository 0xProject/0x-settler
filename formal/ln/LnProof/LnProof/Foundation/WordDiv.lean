import LnProof.Foundation.Word
import Common.Word

open FormalYul
open FormalYul.Preservation

/-!
# Shift and division transports

Floor sandwiches for the arithmetic/logical shifts at the literal shift
amounts the body uses, the `evmSdiv` ↔ `Int.tdiv` transport, and the
cross-multiplied monotonicity of truncated division.
-/

namespace LnYul

/-! ## `evmSar` floor sandwiches (one instance per literal shift amount) -/

section Sar

/-- Helper macro-by-hand: each instance proves
`int256 (evmSar s w) * 2^s ≤ int256 w < int256 (evmSar s w) * 2^s + 2^s`
together with the result being a valid word. -/

theorem evmSar_sandwich_72 {w : Nat} (h : w < 2 ^ 256) :
    evmSar 72 w < 2 ^ 256 ∧
      int256 (evmSar 72 w) * 4722366482869645213696 ≤ int256 w ∧
      int256 w < int256 (evmSar 72 w) * 4722366482869645213696 + 4722366482869645213696 := by
  obtain ⟨h1, h2, h3⟩ := Common.Word.evmSar_sandwich (s := 72) (by norm_num) h
  norm_num at h2 h3
  exact ⟨h1, by linarith, by linarith⟩

theorem evmSar_sandwich_88 {w : Nat} (h : w < 2 ^ 256) :
    evmSar 88 w < 2 ^ 256 ∧
      int256 (evmSar 88 w) * 309485009821345068724781056 ≤ int256 w ∧
      int256 w < int256 (evmSar 88 w) * 309485009821345068724781056 + 309485009821345068724781056 := by
  obtain ⟨h1, h2, h3⟩ := Common.Word.evmSar_sandwich (s := 88) (by norm_num) h
  norm_num at h2 h3
  exact ⟨h1, by linarith, by linarith⟩

theorem evmSar_sandwich_90 {w : Nat} (h : w < 2 ^ 256) :
    evmSar 90 w < 2 ^ 256 ∧
      int256 (evmSar 90 w) * 1237940039285380274899124224 ≤ int256 w ∧
      int256 w < int256 (evmSar 90 w) * 1237940039285380274899124224 + 1237940039285380274899124224 := by
  obtain ⟨h1, h2, h3⟩ := Common.Word.evmSar_sandwich (s := 90) (by norm_num) h
  norm_num at h2 h3
  exact ⟨h1, by linarith, by linarith⟩

theorem evmSar_sandwich_95 {w : Nat} (h : w < 2 ^ 256) :
    evmSar 95 w < 2 ^ 256 ∧
      int256 (evmSar 95 w) * 39614081257132168796771975168 ≤ int256 w ∧
      int256 w < int256 (evmSar 95 w) * 39614081257132168796771975168 + 39614081257132168796771975168 := by
  obtain ⟨h1, h2, h3⟩ := Common.Word.evmSar_sandwich (s := 95) (by norm_num) h
  norm_num at h2 h3
  exact ⟨h1, by linarith, by linarith⟩

theorem evmSar_sandwich_87 {w : Nat} (h : w < 2 ^ 256) :
    evmSar 87 w < 2 ^ 256 ∧
      int256 (evmSar 87 w) * 154742504910672534362390528 ≤ int256 w ∧
      int256 w < int256 (evmSar 87 w) * 154742504910672534362390528 + 154742504910672534362390528 := by
  obtain ⟨h1, h2, h3⟩ := Common.Word.evmSar_sandwich (s := 87) (by norm_num) h
  norm_num at h2 h3
  exact ⟨h1, by linarith, by linarith⟩

theorem evmSar_sandwich_97 {w : Nat} (h : w < 2 ^ 256) :
    evmSar 97 w < 2 ^ 256 ∧
      int256 (evmSar 97 w) * 158456325028528675187087900672 ≤ int256 w ∧
      int256 w < int256 (evmSar 97 w) * 158456325028528675187087900672 + 158456325028528675187087900672 := by
  obtain ⟨h1, h2, h3⟩ := Common.Word.evmSar_sandwich (s := 97) (by norm_num) h
  norm_num at h2 h3
  exact ⟨h1, by linarith, by linarith⟩

theorem evmSar_sandwich_113 {w : Nat} (h : w < 2 ^ 256) :
    evmSar 113 w < 2 ^ 256 ∧
      int256 (evmSar 113 w) * 10384593717069655257060992658440192 ≤ int256 w ∧
      int256 w < int256 (evmSar 113 w) * 10384593717069655257060992658440192 + 10384593717069655257060992658440192 := by
  obtain ⟨h1, h2, h3⟩ := Common.Word.evmSar_sandwich (s := 113) (by norm_num) h
  norm_num at h2 h3
  exact ⟨h1, by linarith, by linarith⟩

end Sar

/-! ## `evmShr` for nonnegative operands at literal shifts -/

theorem evmShr_eq_div_84 {w : Nat} (h : w < 2 ^ 256) : evmShr 84 w = w / 2 ^ 84 :=
  Common.Word.evmShr_eq_div (by norm_num) h

theorem evmShr_eq_div_104 {w : Nat} (h : w < 2 ^ 256) : evmShr 104 w = w / 2 ^ 104 :=
  Common.Word.evmShr_eq_div (by norm_num) h

theorem evmShr_eq_div_160 {w : Nat} (h : w < 2 ^ 256) : evmShr 160 w = w / 2 ^ 160 :=
  Common.Word.evmShr_eq_div (by norm_num) h

theorem evmShr_lt {s : Nat} {w : Nat} (_h : w < 2 ^ 256) : evmShr s w < 2 ^ 256 :=
  Common.Word.evmShr_lt s w

theorem evmShl_lt (s w : Nat) : evmShl s w < 2 ^ 256 := Common.Word.evmShl_lt s w

theorem evmSdiv_lt (a b : Nat) : evmSdiv a b < 2 ^ 256 := by
  unfold evmSdiv u256
  simp only [word_mod_eq]
  repeat' split
  all_goals omega

/-! ## `evmShl` transports -/

/-- Unwrapped left shift when the product genuinely fits (variable shift,
used by the clz normalization). -/
theorem evmShl_eq {s : Nat} (hs : s < 256) {w : Nat} (h : w * 2 ^ s < 2 ^ 256) :
    evmShl s w = w * 2 ^ s := Common.Word.evmShl_eq hs h

/-- Signed left shift by 100 (the `z` numerator). -/
theorem evmShl_transport_100 {w : Nat} (hw : w < 2 ^ 256)
    (h1 : -(2 ^ 255) ≤ int256 w * 1267650600228229401496703205376) (h2 : int256 w * 1267650600228229401496703205376 < 2 ^ 255) :
    int256 (evmShl 100 w) = int256 w * 1267650600228229401496703205376 := by
  have he : evmShl 100 w = (w * 2 ^ 100) % 2 ^ 256 := by
    unfold evmShl u256
    simp only [word_mod_eq, Nat.reducePow, Nat.reduceMod]
    split <;> omega
  rw [he]
  refine toInt_wrap ?_ h1 h2
  have hc : ((w * 2 ^ 100 : Nat) : Int) = (w : Int) * 1267650600228229401496703205376 := by
    omega
  rw [hc, Int.mul_emod, toInt_mod_cong hw, ← Int.mul_emod]

/-! ## `evmSdiv` characterization -/

/-- Decoding helpers for `evmSdiv` results. -/
theorem toInt_u256_of_small {q : Nat} (h : q < 2 ^ 255) : int256 (u256 q) = (q : Int) := by
  unfold int256 u256
  simp only [word_mod_eq, ipow256] at *
  split <;> omega

theorem toInt_u256_neg {q : Nat} (h : q ≤ 2 ^ 255) :
    int256 (u256 (WORD_MOD - q)) = -(q : Int) := by
  unfold int256 u256
  simp only [word_mod_eq, ipow256] at *
  split <;> omega

/-- Sign-pinned semantics of `evmSdiv`: one lemma per sign pattern, with the
quotient expressed over `Int.toNat` magnitudes so that division terms unify
syntactically downstream. -/
theorem evmSdiv_pos_pos {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h1 : 0 ≤ int256 a) (h2 : 0 < int256 b) :
    int256 (evmSdiv a b) = (((int256 a).toNat / (int256 b).toNat : Nat) : Int) := by
  have hna : ¬ 2 ^ 255 ≤ a := by
    unfold int256 at h1; simp only [ipow256] at *; split at h1 <;> omega
  have hnb : ¬ 2 ^ 255 ≤ b := by
    unfold int256 at h2; simp only [ipow256] at *; split at h2 <;> omega
  have hb0 : ¬ b = 0 := by
    unfold int256 at h2; split at h2 <;> omega
  have ea : (int256 a).toNat = a := by
    unfold int256; simp only [ipow256] at *; split <;> omega
  have eb : (int256 b).toNat = b := by
    unfold int256; simp only [ipow256] at *; split <;> omega
  unfold evmSdiv
  simp only [u256_of_lt ha, u256_of_lt hb, decide_eq_false hna, decide_eq_false hnb,
    Bool.false_eq_true, 
    if_true, if_false, if_neg hb0, ea, eb]
  have hq : a / b < 2 ^ 255 := by
    have := Nat.div_le_self a b
    omega
  rw [toInt_u256_of_small hq]

theorem evmSdiv_neg_pos {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h1 : int256 a < 0) (hmin : -(2 ^ 255) < int256 a) (h2 : 0 < int256 b) :
    int256 (evmSdiv a b) = -(((- int256 a).toNat / (int256 b).toNat : Nat) : Int) := by
  have hna : 2 ^ 255 ≤ a := by
    unfold int256 at h1; simp only [ipow255, ipow256] at *; split at h1 <;> omega
  have hnb : ¬ 2 ^ 255 ≤ b := by
    unfold int256 at h2; simp only [ipow255, ipow256] at *; split at h2 <;> omega
  have hb0 : ¬ b = 0 := by
    unfold int256 at h2; split at h2 <;> omega
  have ea : (- int256 a).toNat = WORD_MOD - a := by
    unfold int256; simp only [word_mod_eq, ipow255, ipow256] at *; split <;> omega
  have eb : (int256 b).toNat = b := by
    unfold int256; simp only [ipow255, ipow256] at *; split <;> omega
  unfold evmSdiv
  simp only [u256_of_lt ha, u256_of_lt hb, decide_eq_true hna, decide_eq_false hnb,
    Bool.false_eq_true, Bool.true_eq_false, 
    if_true, if_false, if_neg hb0, ea, eb]
  have hq : (WORD_MOD - a) / b ≤ 2 ^ 255 := by
    have h3 : WORD_MOD - a ≤ 2 ^ 255 := by
      unfold int256 at hmin; simp only [word_mod_eq, ipow255, ipow256] at *
      split at hmin <;> omega
    have := Nat.div_le_self (WORD_MOD - a) b
    omega
  rw [toInt_u256_neg hq]

theorem evmSdiv_pos_neg {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h1 : 0 ≤ int256 a) (h2 : int256 b < 0) :
    int256 (evmSdiv a b) = -(((int256 a).toNat / (- int256 b).toNat : Nat) : Int) := by
  have hna : ¬ 2 ^ 255 ≤ a := by
    unfold int256 at h1; simp only [ipow256] at *; split at h1 <;> omega
  have hnb : 2 ^ 255 ≤ b := by
    unfold int256 at h2; simp only [ipow256] at *; split at h2 <;> omega
  have hb0 : ¬ b = 0 := by
    intro h; subst h; simp only [] at hnb; omega
  have ea : (int256 a).toNat = a := by
    unfold int256; simp only [ipow256] at *; split <;> omega
  have eb : (- int256 b).toNat = WORD_MOD - b := by
    unfold int256; simp only [word_mod_eq, ipow256] at *; split <;> omega
  unfold evmSdiv
  simp only [u256_of_lt ha, u256_of_lt hb, decide_eq_false hna, decide_eq_true hnb,
    Bool.false_eq_true, 
    if_true, if_false, if_neg hb0, ea, eb]
  have hq : a / (WORD_MOD - b) ≤ 2 ^ 255 := by
    have h3 : a < 2 ^ 255 := by
      unfold int256 at h1; simp only [ipow256] at *; split at h1 <;> omega
    have := Nat.div_le_self a (WORD_MOD - b)
    omega
  rw [toInt_u256_neg hq]

theorem evmSdiv_neg_neg {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h1 : int256 a < 0) (hmin : -(2 ^ 255) < int256 a) (h2 : int256 b < 0) :
    int256 (evmSdiv a b) = (((- int256 a).toNat / (- int256 b).toNat : Nat) : Int) := by
  have hna : 2 ^ 255 ≤ a := by
    unfold int256 at h1; simp only [ipow255, ipow256] at *; split at h1 <;> omega
  have hnb : 2 ^ 255 ≤ b := by
    unfold int256 at h2; simp only [ipow255, ipow256] at *; split at h2 <;> omega
  have hb0 : ¬ b = 0 := by
    intro h; subst h; simp only [] at hnb; omega
  have ea : (- int256 a).toNat = WORD_MOD - a := by
    unfold int256; simp only [word_mod_eq, ipow255, ipow256] at *; split <;> omega
  have eb : (- int256 b).toNat = WORD_MOD - b := by
    unfold int256; simp only [word_mod_eq, ipow255, ipow256] at *; split <;> omega
  unfold evmSdiv
  simp only [u256_of_lt ha, u256_of_lt hb, decide_eq_true hna, decide_eq_true hnb,
    
    if_true, if_neg hb0, ea, eb]
  have hq : (WORD_MOD - a) / (WORD_MOD - b) < 2 ^ 255 := by
    have h3 : WORD_MOD - a ≤ 2 ^ 255 := by
      unfold int256 at hmin; simp only [word_mod_eq, ipow255, ipow256] at *
      split at hmin <;> omega
    have := Nat.div_le_self (WORD_MOD - a) (WORD_MOD - b)
    have h4 : ¬ WORD_MOD - a = 2 ^ 255 ∨ True := Or.inr trivial
    simp only [word_mod_eq, ipow255] at *
    omega
  rw [toInt_u256_of_small hq]

/-- Cross-multiplied monotonicity of Nat division. -/
theorem nat_div_cross_mono {a b c d : Nat} (hb : 0 < b) (hd : 0 < d)
    (h : a * d ≤ c * b) : a / b ≤ c / d := Common.Word.nat_div_cross_mono hb hd h

end LnYul
