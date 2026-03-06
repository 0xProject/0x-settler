/-
  Shared EVM simplification lemmas for bridging EVM model operations to Nat arithmetic.

  These lemmas strip u256 wrappers and reduce evmAdd/evmSub/evmMul/evmDiv/evmShl/evmShr/evmAnd
  etc. to their Nat equivalents under appropriate bounds conditions.

  Used by: CbrtComposition, GeneratedCbrt512Spec, and other bridge proofs.
-/
import Cbrt512Proof.GeneratedCbrt512Model

namespace Cbrt512Spec

open Cbrt512GeneratedModel

theorem u256_id' (x : Nat) (hx : x < WORD_MOD) : u256 x = x :=
  Nat.mod_eq_of_lt hx

theorem evmSub_eq_of_le (a b : Nat) (ha : a < WORD_MOD) (hb : b ≤ a) :
    evmSub a b = a - b := by
  unfold evmSub u256
  simp only [Nat.mod_eq_of_lt ha]
  have hb_lt : b < WORD_MOD := Nat.lt_of_le_of_lt hb ha
  simp only [Nat.mod_eq_of_lt hb_lt]
  have h : a + WORD_MOD - b < 2 * WORD_MOD := by omega
  rw [show a + WORD_MOD - b = (a - b) + WORD_MOD from by omega]
  simp [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : a - b < WORD_MOD)]

theorem evmDiv_eq' (a b : Nat) (ha : a < WORD_MOD) (hb : 0 < b) (hb' : b < WORD_MOD) :
    evmDiv a b = a / b := by
  unfold evmDiv u256
  simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb', Nat.ne_of_gt hb]

theorem evmMod_eq' (a b : Nat) (ha : a < WORD_MOD) (hb : 0 < b) (hb' : b < WORD_MOD) :
    evmMod a b = a % b := by
  unfold evmMod u256
  simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb', Nat.ne_of_gt hb]

theorem evmMul_eq' (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmMul a b = (a * b) % WORD_MOD := by
  unfold evmMul u256; simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem evmOr_eq' (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmOr a b = a ||| b := by
  unfold evmOr u256; simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem evmAnd_eq' (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmAnd a b = a &&& b := by
  unfold evmAnd u256; simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem evmShr_eq' (s v : Nat) (hs : s < 256) (hv : v < WORD_MOD) :
    evmShr s v = v / 2 ^ s := by
  have hs' : s < WORD_MOD := by unfold WORD_MOD; omega
  unfold evmShr; simp [u256_id' s hs', u256_id' v hv, hs]

theorem evmShl_eq' (s v : Nat) (hs : s < 256) (hv : v < WORD_MOD) :
    evmShl s v = (v * 2 ^ s) % WORD_MOD := by
  have hs' : s < WORD_MOD := by unfold WORD_MOD; omega
  unfold evmShl u256
  simp [Nat.mod_eq_of_lt hs', Nat.mod_eq_of_lt hv, hs]

theorem evmAdd_eq' (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD)
    (hsum : a + b < WORD_MOD) :
    evmAdd a b = a + b := by
  unfold evmAdd u256
  simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hsum]

theorem evmLt_eq' (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmLt a b = if a < b then 1 else 0 := by
  unfold evmLt u256; simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem evmEq_eq' (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmEq a b = if a = b then 1 else 0 := by
  unfold evmEq u256; simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem evmGt_eq' (a b : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD) :
    evmGt a b = if a > b then 1 else 0 := by
  unfold evmGt u256; simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem evmNot_eq' (a : Nat) (ha : a < WORD_MOD) :
    evmNot a = WORD_MOD - 1 - a := by
  unfold evmNot
  simp only [u256_id' a ha]

theorem evmMulmod_eq' (a b n : Nat) (ha : a < WORD_MOD) (hb : b < WORD_MOD)
    (hn_pos : 0 < n) (hn : n < WORD_MOD) :
    evmMulmod a b n = (a * b) % n := by
  unfold evmMulmod u256
  simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hn, Nat.ne_of_gt hn_pos]

end Cbrt512Spec
