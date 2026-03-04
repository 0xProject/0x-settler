/-
  Bridge from model_cbrt512_evm to icbrt: specification layer.

  Part 1: EVM simplification lemmas (shared with wrapper/up specs).
  Part 2: Core algorithm bridge — model_cbrt512_evm within 1ulp of icbrt.
  Part 3: Composition with icbrt.

  Architecture: model_cbrt512_evm →[direct EVM bridge]→ icbrt ± 1

  Note: The auto-generated norm model (model_cbrt512) uses unbounded Nat operations
  which do NOT match EVM uint256 semantics. Therefore we prove the EVM model correct
  directly, without factoring through the norm model.
-/
import Cbrt512Proof.Cbrt512Correct
import Cbrt512Proof.GeneratedCbrt512Model
import Cbrt512Proof.CbrtDenormalization
import Cbrt512Proof.CbrtNormalization
import Cbrt512Proof.CbrtBaseCase
import Cbrt512Proof.CbrtKaratsubaQuotient
import Cbrt512Proof.CbrtComposition

namespace Cbrt512Spec

-- ============================================================================
-- Section 1: EVM simplification lemmas
-- ============================================================================

section EvmNormBridge
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
  simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb', Nat.ne_of_gt hb,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self a b) ha)]

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

end EvmNormBridge

-- ============================================================================
-- Section 2: Core algorithm correctness
-- model_cbrt512_evm returns a value within 1ulp of icbrt for x_hi > 0.
-- ============================================================================

open Cbrt512GeneratedModel

/-- The 512-bit _cbrt EVM model returns a value within 1ulp of icbrt.
    For x_hi > 0 and both x_hi, x_lo < 2^256:
      icbrt(x_hi * 2^256 + x_lo) ≤ r ≤ icbrt(x_hi * 2^256 + x_lo) + 1
    and r < WORD_MOD, r³ < WORD_MOD² (so cube512_correct applies).
    Additionally, when r overshoots (r³ > x), x is not a perfect cube.
    This ensures the cbrtUp wrapper's cube-and-compare correction is sound. -/
theorem model_cbrt512_evm_within_1ulp (x_hi x_lo : Nat)
    (hxhi_pos : 0 < x_hi) (hxhi : x_hi < 2 ^ 256) (hxlo : x_lo < 2 ^ 256) :
    let x := x_hi * 2 ^ 256 + x_lo
    let r := model_cbrt512_evm x_hi x_lo
    icbrt x ≤ r ∧ r ≤ icbrt x + 1 ∧ r < WORD_MOD ∧ r * r * r < WORD_MOD * WORD_MOD
    ∧ r + 1 < WORD_MOD
    ∧ (r * r * r > x → icbrt x * icbrt x * icbrt x < x) := by
  /- Proof strategy:
     1. Compute shift = clz(x_hi)/3, normalize x → x_norm = x * 2^(3*shift)
     2. Use composition_within_1ulp on x_norm to get r_norm within 1ulp of icbrt(x_norm)
     3. Denormalize: r = r_norm >> shift gives icbrt(x) ≤ r ≤ icbrt(x) + 1
     4. Derive remaining bounds (r < W, r³ < W², r+1 < W, overshoot property)
  -/
  sorry

end Cbrt512Spec
