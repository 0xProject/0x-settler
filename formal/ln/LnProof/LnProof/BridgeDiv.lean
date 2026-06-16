import LnProof.Bridge

/-!
# Shift and division transports

Floor sandwiches for the arithmetic/logical shifts at the literal shift
amounts the model uses, the `evmSdiv` ↔ `Int.tdiv` transport, and the
cross-multiplied monotonicity of truncated division.
-/

namespace LnGeneratedModel

/-! ## `evmSar` floor sandwiches (one instance per literal shift amount) -/

section Sar

/-- Helper macro-by-hand: each instance proves
`toInt (evmSar s w) * 2^s ≤ toInt w < toInt (evmSar s w) * 2^s + 2^s`
together with the result being a valid word. -/

theorem evmSar_sandwich_72 {w : Nat} (h : w < 2 ^ 256) :
    evmSar 72 w < 2 ^ 256 ∧
      toInt (evmSar 72 w) * 4722366482869645213696 ≤ toInt w ∧
      toInt w < toInt (evmSar 72 w) * 4722366482869645213696 + 4722366482869645213696 := by
  unfold evmSar u256 toInt
  simp only [word_mod_eq, ipow256, Nat.reducePow, Nat.reduceMod]
  repeat' split
  all_goals omega

theorem evmSar_sandwich_88 {w : Nat} (h : w < 2 ^ 256) :
    evmSar 88 w < 2 ^ 256 ∧
      toInt (evmSar 88 w) * 309485009821345068724781056 ≤ toInt w ∧
      toInt w < toInt (evmSar 88 w) * 309485009821345068724781056 + 309485009821345068724781056 := by
  unfold evmSar u256 toInt
  simp only [word_mod_eq, ipow256, Nat.reducePow, Nat.reduceMod]
  repeat' split
  all_goals omega

theorem evmSar_sandwich_90 {w : Nat} (h : w < 2 ^ 256) :
    evmSar 90 w < 2 ^ 256 ∧
      toInt (evmSar 90 w) * 1237940039285380274899124224 ≤ toInt w ∧
      toInt w < toInt (evmSar 90 w) * 1237940039285380274899124224 + 1237940039285380274899124224 := by
  unfold evmSar u256 toInt
  simp only [word_mod_eq, ipow256, Nat.reducePow, Nat.reduceMod]
  repeat' split
  all_goals omega

theorem evmSar_sandwich_95 {w : Nat} (h : w < 2 ^ 256) :
    evmSar 95 w < 2 ^ 256 ∧
      toInt (evmSar 95 w) * 39614081257132168796771975168 ≤ toInt w ∧
      toInt w < toInt (evmSar 95 w) * 39614081257132168796771975168 + 39614081257132168796771975168 := by
  unfold evmSar u256 toInt
  simp only [word_mod_eq, ipow256, Nat.reducePow, Nat.reduceMod]
  repeat' split
  all_goals omega

theorem evmSar_sandwich_87 {w : Nat} (h : w < 2 ^ 256) :
    evmSar 87 w < 2 ^ 256 ∧
      toInt (evmSar 87 w) * 154742504910672534362390528 ≤ toInt w ∧
      toInt w < toInt (evmSar 87 w) * 154742504910672534362390528 + 154742504910672534362390528 := by
  unfold evmSar u256 toInt
  simp only [word_mod_eq, ipow256, Nat.reducePow, Nat.reduceMod]
  repeat' split
  all_goals omega

theorem evmSar_sandwich_97 {w : Nat} (h : w < 2 ^ 256) :
    evmSar 97 w < 2 ^ 256 ∧
      toInt (evmSar 97 w) * 158456325028528675187087900672 ≤ toInt w ∧
      toInt w < toInt (evmSar 97 w) * 158456325028528675187087900672 + 158456325028528675187087900672 := by
  unfold evmSar u256 toInt
  simp only [word_mod_eq, ipow256, Nat.reducePow, Nat.reduceMod]
  repeat' split
  all_goals omega

theorem evmSar_sandwich_113 {w : Nat} (h : w < 2 ^ 256) :
    evmSar 113 w < 2 ^ 256 ∧
      toInt (evmSar 113 w) * 10384593717069655257060992658440192 ≤ toInt w ∧
      toInt w < toInt (evmSar 113 w) * 10384593717069655257060992658440192 + 10384593717069655257060992658440192 := by
  unfold evmSar u256 toInt
  simp only [word_mod_eq, ipow256, Nat.reducePow, Nat.reduceMod]
  repeat' split
  all_goals omega

end Sar

/-! ## `evmShr` for nonnegative operands at literal shifts -/

theorem evmShr_eq_div_84 {w : Nat} (h : w < 2 ^ 256) : evmShr 84 w = w / 2 ^ 84 := by
  unfold evmShr u256
  simp only [word_mod_eq, Nat.reducePow, Nat.reduceMod]
  split <;> omega

theorem evmShr_eq_div_104 {w : Nat} (h : w < 2 ^ 256) : evmShr 104 w = w / 2 ^ 104 := by
  unfold evmShr u256
  simp only [word_mod_eq, Nat.reducePow, Nat.reduceMod]
  split <;> omega

theorem evmShr_eq_div_160 {w : Nat} (h : w < 2 ^ 256) : evmShr 160 w = w / 2 ^ 160 := by
  unfold evmShr u256
  simp only [word_mod_eq, Nat.reducePow, Nat.reduceMod]
  split <;> omega

theorem evmShr_lt {s : Nat} {w : Nat} (_h : w < 2 ^ 256) : evmShr s w < 2 ^ 256 := by
  unfold evmShr u256
  simp only [word_mod_eq]
  split
  · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  · omega

theorem evmShl_lt (s w : Nat) : evmShl s w < 2 ^ 256 := by
  unfold evmShl u256
  simp only [word_mod_eq]
  split <;> omega

theorem evmSdiv_lt (a b : Nat) : evmSdiv a b < 2 ^ 256 := by
  unfold evmSdiv u256
  simp only [word_mod_eq]
  repeat' split
  all_goals omega

/-! ## `evmShl` transports -/

/-- Unwrapped left shift when the product genuinely fits (variable shift,
used by the clz normalization). -/
theorem evmShl_eq {s : Nat} (hs : s < 256) {w : Nat} (h : w * 2 ^ s < 2 ^ 256) :
    evmShl s w = w * 2 ^ s := by
  unfold evmShl u256
  simp only [word_mod_eq]
  have hs2 : s % 2 ^ 256 = s := Nat.mod_eq_of_lt (by omega)
  have hpos : 0 < 2 ^ s := Nat.two_pow_pos s
  have hw : w < 2 ^ 256 := by
    have h1 : w * 1 ≤ w * 2 ^ s := Nat.mul_le_mul_left w hpos
    omega
  rw [hs2, if_pos hs, Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt h]

/-- Signed left shift by 100 (the `z` numerator). -/
theorem evmShl_transport_100 {w : Nat} (hw : w < 2 ^ 256)
    (h1 : -(2 ^ 255) ≤ toInt w * 1267650600228229401496703205376) (h2 : toInt w * 1267650600228229401496703205376 < 2 ^ 255) :
    toInt (evmShl 100 w) = toInt w * 1267650600228229401496703205376 := by
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
theorem toInt_u256_of_small {q : Nat} (h : q < 2 ^ 255) : toInt (u256 q) = (q : Int) := by
  unfold toInt u256
  simp only [word_mod_eq, ipow256] at *
  split <;> omega

theorem toInt_u256_neg {q : Nat} (h : q ≤ 2 ^ 255) :
    toInt (u256 (WORD_MOD - q)) = -(q : Int) := by
  unfold toInt u256
  simp only [word_mod_eq, ipow256] at *
  split <;> omega

/-- Sign-pinned semantics of `evmSdiv`: one lemma per sign pattern, with the
quotient expressed over `Int.toNat` magnitudes so that division terms unify
syntactically downstream. -/
theorem evmSdiv_pos_pos {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h1 : 0 ≤ toInt a) (h2 : 0 < toInt b) :
    toInt (evmSdiv a b) = (((toInt a).toNat / (toInt b).toNat : Nat) : Int) := by
  have hna : ¬ 2 ^ 255 ≤ a := by
    unfold toInt at h1; simp only [ipow256] at *; split at h1 <;> omega
  have hnb : ¬ 2 ^ 255 ≤ b := by
    unfold toInt at h2; simp only [ipow256] at *; split at h2 <;> omega
  have hb0 : ¬ b = 0 := by
    unfold toInt at h2; split at h2 <;> omega
  have ea : (toInt a).toNat = a := by
    unfold toInt; simp only [ipow256] at *; split <;> omega
  have eb : (toInt b).toNat = b := by
    unfold toInt; simp only [ipow256] at *; split <;> omega
  unfold evmSdiv
  simp only [u256_of_lt ha, u256_of_lt hb, decide_eq_false hna, decide_eq_false hnb,
    Bool.false_eq_true, 
    if_true, if_false, if_neg hb0, ea, eb]
  have hq : a / b < 2 ^ 255 := by
    have := Nat.div_le_self a b
    omega
  rw [toInt_u256_of_small hq]

theorem evmSdiv_neg_pos {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h1 : toInt a < 0) (hmin : -(2 ^ 255) < toInt a) (h2 : 0 < toInt b) :
    toInt (evmSdiv a b) = -(((- toInt a).toNat / (toInt b).toNat : Nat) : Int) := by
  have hna : 2 ^ 255 ≤ a := by
    unfold toInt at h1; simp only [ipow255, ipow256] at *; split at h1 <;> omega
  have hnb : ¬ 2 ^ 255 ≤ b := by
    unfold toInt at h2; simp only [ipow255, ipow256] at *; split at h2 <;> omega
  have hb0 : ¬ b = 0 := by
    unfold toInt at h2; split at h2 <;> omega
  have ea : (- toInt a).toNat = WORD_MOD - a := by
    unfold toInt; simp only [word_mod_eq, ipow255, ipow256] at *; split <;> omega
  have eb : (toInt b).toNat = b := by
    unfold toInt; simp only [ipow255, ipow256] at *; split <;> omega
  unfold evmSdiv
  simp only [u256_of_lt ha, u256_of_lt hb, decide_eq_true hna, decide_eq_false hnb,
    Bool.false_eq_true, Bool.true_eq_false, 
    if_true, if_false, if_neg hb0, ea, eb]
  have hq : (WORD_MOD - a) / b ≤ 2 ^ 255 := by
    have h3 : WORD_MOD - a ≤ 2 ^ 255 := by
      unfold toInt at hmin; simp only [word_mod_eq, ipow255, ipow256] at *
      split at hmin <;> omega
    have := Nat.div_le_self (WORD_MOD - a) b
    omega
  rw [toInt_u256_neg hq]

theorem evmSdiv_pos_neg {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h1 : 0 ≤ toInt a) (h2 : toInt b < 0) :
    toInt (evmSdiv a b) = -(((toInt a).toNat / (- toInt b).toNat : Nat) : Int) := by
  have hna : ¬ 2 ^ 255 ≤ a := by
    unfold toInt at h1; simp only [ipow256] at *; split at h1 <;> omega
  have hnb : 2 ^ 255 ≤ b := by
    unfold toInt at h2; simp only [ipow256] at *; split at h2 <;> omega
  have hb0 : ¬ b = 0 := by
    intro h; subst h; simp only [] at hnb; omega
  have ea : (toInt a).toNat = a := by
    unfold toInt; simp only [ipow256] at *; split <;> omega
  have eb : (- toInt b).toNat = WORD_MOD - b := by
    unfold toInt; simp only [word_mod_eq, ipow256] at *; split <;> omega
  unfold evmSdiv
  simp only [u256_of_lt ha, u256_of_lt hb, decide_eq_false hna, decide_eq_true hnb,
    Bool.false_eq_true, 
    if_true, if_false, if_neg hb0, ea, eb]
  have hq : a / (WORD_MOD - b) ≤ 2 ^ 255 := by
    have h3 : a < 2 ^ 255 := by
      unfold toInt at h1; simp only [ipow256] at *; split at h1 <;> omega
    have := Nat.div_le_self a (WORD_MOD - b)
    omega
  rw [toInt_u256_neg hq]

theorem evmSdiv_neg_neg {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h1 : toInt a < 0) (hmin : -(2 ^ 255) < toInt a) (h2 : toInt b < 0) :
    toInt (evmSdiv a b) = (((- toInt a).toNat / (- toInt b).toNat : Nat) : Int) := by
  have hna : 2 ^ 255 ≤ a := by
    unfold toInt at h1; simp only [ipow255, ipow256] at *; split at h1 <;> omega
  have hnb : 2 ^ 255 ≤ b := by
    unfold toInt at h2; simp only [ipow255, ipow256] at *; split at h2 <;> omega
  have hb0 : ¬ b = 0 := by
    intro h; subst h; simp only [] at hnb; omega
  have ea : (- toInt a).toNat = WORD_MOD - a := by
    unfold toInt; simp only [word_mod_eq, ipow255, ipow256] at *; split <;> omega
  have eb : (- toInt b).toNat = WORD_MOD - b := by
    unfold toInt; simp only [word_mod_eq, ipow255, ipow256] at *; split <;> omega
  unfold evmSdiv
  simp only [u256_of_lt ha, u256_of_lt hb, decide_eq_true hna, decide_eq_true hnb,
    
    if_true, if_neg hb0, ea, eb]
  have hq : (WORD_MOD - a) / (WORD_MOD - b) < 2 ^ 255 := by
    have h3 : WORD_MOD - a ≤ 2 ^ 255 := by
      unfold toInt at hmin; simp only [word_mod_eq, ipow255, ipow256] at *
      split at hmin <;> omega
    have := Nat.div_le_self (WORD_MOD - a) (WORD_MOD - b)
    have h4 : ¬ WORD_MOD - a = 2 ^ 255 ∨ True := Or.inr trivial
    simp only [word_mod_eq, ipow255] at *
    omega
  rw [toInt_u256_of_small hq]

/-- Cross-multiplied monotonicity of Nat division. -/
theorem nat_div_cross_mono {a b c d : Nat} (hb : 0 < b) (hd : 0 < d)
    (h : a * d ≤ c * b) : a / b ≤ c / d := by
  rw [Nat.le_div_iff_mul_le hd]
  have h1 : a / b * b ≤ a := Nat.div_mul_le_self a b
  have h2 : a / b * b * d ≤ a * d := Nat.mul_le_mul_right d h1
  have h3 : a / b * b * d ≤ c * b := Nat.le_trans h2 h
  have h4 : a / b * d * b ≤ c * b := by
    have : a / b * b * d = a / b * d * b := by
      rw [Nat.mul_assoc, Nat.mul_comm b d, ← Nat.mul_assoc]
    omega
  exact Nat.le_of_mul_le_mul_right h4 hb

end LnGeneratedModel
