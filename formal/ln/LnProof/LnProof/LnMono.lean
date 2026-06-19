import LnProof.LnYul

/-!
# Monotonicity certificates for the generated Ln model

`Ln.lnWad` maps a wad-basis input to a ray-basis `int256` encoded as a
two's-complement word, so ordering statements use the sign-bit-biased
unsigned comparison `sle`.

Monotonicity of `lnWad` over its whole domain `0 < x < 2^255` decomposes as:

* adjacent inputs that share the Q103 mantissa and exponent return the same
  word (the model is a function of the mantissa/exponent pair);
* within an octave, the mantissa-to-result map is nondecreasing -- proven in
  `LnProof.StepMono`/`LnProof.ZOctave`/`LnProof.OctaveMono` from the
  polynomial certificates in `LnProof.Certs`;
* across the 254 clz seams, the adjacent pair `(2^t - 1, 2^t)` is checked
  here by exact evaluation of the generated model;
* the single corrected point `x = 10^18` (whose exact result, 0, is the only
  integer value of the function) is checked here together with its
  neighbors.

The theorems in this file are the finitely-decidable legs of that argument,
evaluated against the same generated model that the FFI fuzz suite checks
against the deployed Solidity. `LnProof.TopMono` composes all of the legs
into `model_ln_wad_mono`, monotonicity over the whole domain.
-/

set_option maxRecDepth 100000
set_option exponentiation.threshold 512

namespace LnYul

private theorem log2_eq_iff {n k : Nat} (h : n ≠ 0) :
    Nat.log2 n = k ↔ 2 ^ k ≤ n ∧ n < 2 ^ (k + 1) := by
  constructor
  · intro hk
    subst hk
    exact ⟨(Nat.le_log2 h).mp (Nat.le_refl _),
      (Nat.log2_lt h).mp (Nat.lt_succ_self _)⟩
  · intro hk
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp ((Nat.log2_lt h).mpr hk.2))
      ((Nat.le_log2 h).mpr hk.1)

/-- Signed (two's complement) `≤` on uint256 words: unsigned comparison with
the sign bit flipped. -/
def sle (a b : Nat) : Bool :=
  decide ((a + 2 ^ 255) % WORD_MOD ≤ (b + 2 ^ 255) % WORD_MOD)

/-- One comparison per clz seam: `f(2^t) ≥ f(2^t - 1)` for `t ∈ [1, 254]`. -/
def seamMono (f : Nat → Nat) : Bool :=
  (List.range 254).all fun t => sle (f (2 ^ (t + 1) - 1)) (f (2 ^ (t + 1)))

private theorem ray_eval_one_wad :
    model_ln_wad_evm (10 ^ 18) = 0 := by
  have hlog : Nat.log2 ((10 : Nat) ^ 18) = 59 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (10 ^ 18) % 2 ^ 256 = 10 ^ 18 by decide]
  simp only [hlog]
  decide

private theorem wad_eval_one_wad :
    model_ln_wad_to_wad_evm (10 ^ 18) = 0 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (10 ^ 18) % 2 ^ 256 = 10 ^ 18 by decide]
  rw [ray_eval_one_wad]
  decide

private theorem ray_eval_one_wad_prev :
    model_ln_wad_evm (10 ^ 18 - 1) = 115792089237316195423570985008687907853269984665640564039457584007912129639935 := by
  have hlog : Nat.log2 ((10 : Nat) ^ 18 - 1) = 59 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (10 ^ 18 - 1) % 2 ^ 256 = 10 ^ 18 - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_one_wad_next :
    model_ln_wad_evm (10 ^ 18 + 1) = 999999999 := by
  have hlog : Nat.log2 ((10 : Nat) ^ 18 + 1) = 59 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (10 ^ 18 + 1) % 2 ^ 256 = 10 ^ 18 + 1 by decide]
  simp only [hlog]
  decide

/-- `lnWad(10**18) = 0` exactly. -/
theorem model_ln_wad_one_wad : model_ln_wad_evm (10 ^ 18) = 0 :=
  ray_eval_one_wad

/-- `lnWadToWad(10**18) = 0` exactly. -/
theorem model_ln_wad_to_wad_one_wad : model_ln_wad_to_wad_evm (10 ^ 18) = 0 :=
  wad_eval_one_wad

/-- The model value immediately below one wad. -/
theorem model_ln_wad_one_wad_prev :
    model_ln_wad_evm (10 ^ 18 - 1) =
      115792089237316195423570985008687907853269984665640564039457584007912129639935 :=
  ray_eval_one_wad_prev

/-- The model value immediately above one wad. -/
theorem model_ln_wad_one_wad_next :
    model_ln_wad_evm (10 ^ 18 + 1) = 999999999 :=
  ray_eval_one_wad_next

/-- The `x = 10**18` correction preserves order against both neighbors. -/
theorem model_ln_wad_one_wad_mono :
    (sle (model_ln_wad_evm (10 ^ 18 - 1)) (model_ln_wad_evm (10 ^ 18))
      && sle (model_ln_wad_evm (10 ^ 18)) (model_ln_wad_evm (10 ^ 18 + 1))) = true := by
  rw [ray_eval_one_wad_prev, ray_eval_one_wad, ray_eval_one_wad_next]
  unfold sle
  decide

private theorem ray_eval_seam_0_lo :
    model_ln_wad_evm (2 ^ (0 + 1) - 1) = 115792089237316195423570985008687907853269984665599117507783691185600805793751 := by
  have hlog : Nat.log2 (2 ^ (0 + 1) - 1) = 0 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (0 + 1) - 1) % 2 ^ 256 = 2 ^ (0 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_0_hi :
    model_ln_wad_evm (2 ^ (0 + 1)) = 115792089237316195423570985008687907853269984665599810654964251130910223025873 := by
  have hlog : Nat.log2 (2 ^ (0 + 1)) = 1 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (0 + 1)) % 2 ^ 256 = 2 ^ (0 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_0_lo :
    model_ln_wad_to_wad_evm (2 ^ (0 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039416137476239236817623 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (0 + 1) - 1) % 2 ^ 256 = 2 ^ (0 + 1) - 1 by decide]
  rw [ray_eval_seam_0_lo]
  decide

private theorem wad_eval_seam_0_hi :
    model_ln_wad_to_wad_evm (2 ^ (0 + 1)) = 115792089237316195423570985008687907853269984665640564039416830623419796762933 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (0 + 1)) % 2 ^ 256 = 2 ^ (0 + 1) by decide]
  rw [ray_eval_seam_0_hi]
  decide

private theorem ray_seam_0 :
    sle (model_ln_wad_evm (2 ^ (0 + 1) - 1)) (model_ln_wad_evm (2 ^ (0 + 1))) = true := by
  rw [ray_eval_seam_0_lo, ray_eval_seam_0_hi]
  unfold sle
  decide

private theorem wad_seam_0 :
    sle (model_ln_wad_to_wad_evm (2 ^ (0 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (0 + 1))) = true := by
  rw [wad_eval_seam_0_lo, wad_eval_seam_0_hi]
  unfold sle
  decide

private theorem ray_eval_seam_1_lo :
    model_ln_wad_evm (2 ^ (1 + 1) - 1) = 115792089237316195423570985008687907853269984665600216120072359295292201038988 := by
  have hlog : Nat.log2 (2 ^ (1 + 1) - 1) = 1 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (1 + 1) - 1) % 2 ^ 256 = 2 ^ (1 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_1_hi :
    model_ln_wad_evm (2 ^ (1 + 1)) = 115792089237316195423570985008687907853269984665600503802144811076219640257994 := by
  have hlog : Nat.log2 (2 ^ (1 + 1)) = 2 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (1 + 1)) % 2 ^ 256 = 2 ^ (1 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_1_lo :
    model_ln_wad_to_wad_evm (2 ^ (1 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039417236088527904927315 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (1 + 1) - 1) % 2 ^ 256 = 2 ^ (1 + 1) - 1 by decide]
  rw [ray_eval_seam_1_lo]
  decide

private theorem wad_eval_seam_1_hi :
    model_ln_wad_to_wad_evm (2 ^ (1 + 1)) = 115792089237316195423570985008687907853269984665640564039417523770600356708242 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (1 + 1)) % 2 ^ 256 = 2 ^ (1 + 1) by decide]
  rw [ray_eval_seam_1_hi]
  decide

private theorem ray_seam_1 :
    sle (model_ln_wad_evm (2 ^ (1 + 1) - 1)) (model_ln_wad_evm (2 ^ (1 + 1))) = true := by
  rw [ray_eval_seam_1_lo, ray_eval_seam_1_hi]
  unfold sle
  decide

private theorem wad_seam_1 :
    sle (model_ln_wad_to_wad_evm (2 ^ (1 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (1 + 1))) = true := by
  rw [wad_eval_seam_1_lo, wad_eval_seam_1_hi]
  unfold sle
  decide

private theorem ray_eval_seam_2_lo :
    model_ln_wad_evm (2 ^ (2 + 1) - 1) = 115792089237316195423570985008687907853269984665601063417932746498905911146494 := by
  have hlog : Nat.log2 (2 ^ (2 + 1) - 1) = 2 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (2 + 1) - 1) % 2 ^ 256 = 2 ^ (2 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_2_hi :
    model_ln_wad_evm (2 ^ (2 + 1)) = 115792089237316195423570985008687907853269984665601196949325371021529057490116 := by
  have hlog : Nat.log2 (2 ^ (2 + 1)) = 3 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (2 + 1)) % 2 ^ 256 = 2 ^ (2 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_2_lo :
    model_ln_wad_to_wad_evm (2 ^ (2 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039418083386388292130928 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (2 + 1) - 1) % 2 ^ 256 = 2 ^ (2 + 1) - 1 by decide]
  rw [ray_eval_seam_2_lo]
  decide

private theorem wad_eval_seam_2_hi :
    model_ln_wad_to_wad_evm (2 ^ (2 + 1)) = 115792089237316195423570985008687907853269984665640564039418216917780916653551 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (2 + 1)) % 2 ^ 256 = 2 ^ (2 + 1) by decide]
  rw [ray_eval_seam_2_hi]
  decide

private theorem ray_seam_2 :
    sle (model_ln_wad_evm (2 ^ (2 + 1) - 1)) (model_ln_wad_evm (2 ^ (2 + 1))) = true := by
  rw [ray_eval_seam_2_lo, ray_eval_seam_2_hi]
  unfold sle
  decide

private theorem wad_seam_2 :
    sle (model_ln_wad_to_wad_evm (2 ^ (2 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (2 + 1))) = true := by
  rw [wad_eval_seam_2_lo, wad_eval_seam_2_hi]
  unfold sle
  decide

private theorem ray_eval_seam_3_lo :
    model_ln_wad_evm (2 ^ (3 + 1) - 1) = 115792089237316195423570985008687907853269984665601825557984793395666801798321 := by
  have hlog : Nat.log2 (2 ^ (3 + 1) - 1) = 3 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (3 + 1) - 1) % 2 ^ 256 = 2 ^ (3 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_3_hi :
    model_ln_wad_evm (2 ^ (3 + 1)) = 115792089237316195423570985008687907853269984665601890096505930966838474722237 := by
  have hlog : Nat.log2 (2 ^ (3 + 1)) = 4 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (3 + 1)) % 2 ^ 256 = 2 ^ (3 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_3_lo :
    model_ln_wad_to_wad_evm (2 ^ (3 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039418845526440339027689 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (3 + 1) - 1) % 2 ^ 256 = 2 ^ (3 + 1) - 1 by decide]
  rw [ray_eval_seam_3_lo]
  decide

private theorem wad_eval_seam_3_hi :
    model_ln_wad_to_wad_evm (2 ^ (3 + 1)) = 115792089237316195423570985008687907853269984665640564039418910064961476598861 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (3 + 1)) % 2 ^ 256 = 2 ^ (3 + 1) by decide]
  rw [ray_eval_seam_3_hi]
  decide

private theorem ray_seam_3 :
    sle (model_ln_wad_evm (2 ^ (3 + 1) - 1)) (model_ln_wad_evm (2 ^ (3 + 1))) = true := by
  rw [ray_eval_seam_3_lo, ray_eval_seam_3_hi]
  unfold sle
  decide

private theorem wad_seam_3 :
    sle (model_ln_wad_to_wad_evm (2 ^ (3 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (3 + 1))) = true := by
  rw [wad_eval_seam_3_lo, wad_eval_seam_3_hi]
  unfold sle
  decide

private theorem ray_eval_seam_4_lo :
    model_ln_wad_evm (2 ^ (4 + 1) - 1) = 115792089237316195423570985008687907853269984665602551494988176331846734958076 := by
  have hlog : Nat.log2 (2 ^ (4 + 1) - 1) = 4 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (4 + 1) - 1) % 2 ^ 256 = 2 ^ (4 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_4_hi :
    model_ln_wad_evm (2 ^ (4 + 1)) = 115792089237316195423570985008687907853269984665602583243686490912147891954358 := by
  have hlog : Nat.log2 (2 ^ (4 + 1)) = 5 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (4 + 1)) % 2 ^ 256 = 2 ^ (4 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_4_lo :
    model_ln_wad_to_wad_evm (2 ^ (4 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039419571463443721963869 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (4 + 1) - 1) % 2 ^ 256 = 2 ^ (4 + 1) - 1 by decide]
  rw [ray_eval_seam_4_lo]
  decide

private theorem wad_eval_seam_4_hi :
    model_ln_wad_to_wad_evm (2 ^ (4 + 1)) = 115792089237316195423570985008687907853269984665640564039419603212142036544170 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (4 + 1)) % 2 ^ 256 = 2 ^ (4 + 1) by decide]
  rw [ray_eval_seam_4_hi]
  decide

private theorem ray_seam_4 :
    sle (model_ln_wad_evm (2 ^ (4 + 1) - 1)) (model_ln_wad_evm (2 ^ (4 + 1))) = true := by
  rw [ray_eval_seam_4_lo, ray_eval_seam_4_hi]
  unfold sle
  decide

private theorem wad_seam_4 :
    sle (model_ln_wad_to_wad_evm (2 ^ (4 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (4 + 1))) = true := by
  rw [wad_eval_seam_4_lo, wad_eval_seam_4_hi]
  unfold sle
  decide

private theorem ray_eval_seam_5_lo :
    model_ln_wad_evm (2 ^ (5 + 1) - 1) = 115792089237316195423570985008687907853269984665603260642510082718288701636968 := by
  have hlog : Nat.log2 (2 ^ (5 + 1) - 1) = 5 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (5 + 1) - 1) % 2 ^ 256 = 2 ^ (5 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_5_hi :
    model_ln_wad_evm (2 ^ (5 + 1)) = 115792089237316195423570985008687907853269984665603276390867050857457309186480 := by
  have hlog : Nat.log2 (2 ^ (5 + 1)) = 6 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (5 + 1)) % 2 ^ 256 = 2 ^ (5 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_5_lo :
    model_ln_wad_to_wad_evm (2 ^ (5 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039420280610965628350311 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (5 + 1) - 1) % 2 ^ 256 = 2 ^ (5 + 1) - 1 by decide]
  rw [ray_eval_seam_5_lo]
  decide

private theorem wad_eval_seam_5_hi :
    model_ln_wad_to_wad_evm (2 ^ (5 + 1)) = 115792089237316195423570985008687907853269984665640564039420296359322596489480 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (5 + 1)) % 2 ^ 256 = 2 ^ (5 + 1) by decide]
  rw [ray_eval_seam_5_hi]
  decide

private theorem ray_seam_5 :
    sle (model_ln_wad_evm (2 ^ (5 + 1) - 1)) (model_ln_wad_evm (2 ^ (5 + 1))) = true := by
  rw [ray_eval_seam_5_lo, ray_eval_seam_5_hi]
  unfold sle
  decide

private theorem wad_seam_5 :
    sle (model_ln_wad_to_wad_evm (2 ^ (5 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (5 + 1))) = true := by
  rw [wad_eval_seam_5_lo, wad_eval_seam_5_hi]
  unfold sle
  decide

private theorem ray_eval_seam_6_lo :
    model_ln_wad_evm (2 ^ (6 + 1) - 1) = 115792089237316195423570985008687907853269984665603961694870149776873853234559 := by
  have hlog : Nat.log2 (2 ^ (6 + 1) - 1) = 6 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (6 + 1) - 1) % 2 ^ 256 = 2 ^ (6 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_6_hi :
    model_ln_wad_evm (2 ^ (6 + 1)) = 115792089237316195423570985008687907853269984665603969538047610802766726418601 := by
  have hlog : Nat.log2 (2 ^ (6 + 1)) = 7 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (6 + 1)) % 2 ^ 256 = 2 ^ (6 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_6_lo :
    model_ln_wad_to_wad_evm (2 ^ (6 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039420981663325695408896 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (6 + 1) - 1) % 2 ^ 256 = 2 ^ (6 + 1) - 1 by decide]
  rw [ray_eval_seam_6_lo]
  decide

private theorem wad_eval_seam_6_hi :
    model_ln_wad_to_wad_evm (2 ^ (6 + 1)) = 115792089237316195423570985008687907853269984665640564039420989506503156434789 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (6 + 1)) % 2 ^ 256 = 2 ^ (6 + 1) by decide]
  rw [ray_eval_seam_6_hi]
  decide

private theorem ray_seam_6 :
    sle (model_ln_wad_evm (2 ^ (6 + 1) - 1)) (model_ln_wad_evm (2 ^ (6 + 1))) = true := by
  rw [ray_eval_seam_6_lo, ray_eval_seam_6_hi]
  unfold sle
  decide

private theorem wad_seam_6 :
    sle (model_ln_wad_to_wad_evm (2 ^ (6 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (6 + 1))) = true := by
  rw [wad_eval_seam_6_lo, wad_eval_seam_6_hi]
  unfold sle
  decide

private theorem ray_eval_seam_7_lo :
    model_ln_wad_evm (2 ^ (7 + 1) - 1) = 115792089237316195423570985008687907853269984665604658771328849611747051332939 := by
  have hlog : Nat.log2 (2 ^ (7 + 1) - 1) = 7 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (7 + 1) - 1) % 2 ^ 256 = 2 ^ (7 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_7_hi :
    model_ln_wad_evm (2 ^ (7 + 1)) = 115792089237316195423570985008687907853269984665604662685228170748076143650723 := by
  have hlog : Nat.log2 (2 ^ (7 + 1)) = 8 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (7 + 1)) % 2 ^ 256 = 2 ^ (7 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_7_lo :
    model_ln_wad_to_wad_evm (2 ^ (7 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039421678739784395243769 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (7 + 1) - 1) % 2 ^ 256 = 2 ^ (7 + 1) - 1 by decide]
  rw [ray_eval_seam_7_lo]
  decide

private theorem wad_eval_seam_7_hi :
    model_ln_wad_to_wad_evm (2 ^ (7 + 1)) = 115792089237316195423570985008687907853269984665640564039421682653683716380099 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (7 + 1)) % 2 ^ 256 = 2 ^ (7 + 1) by decide]
  rw [ray_eval_seam_7_hi]
  decide

private theorem ray_seam_7 :
    sle (model_ln_wad_evm (2 ^ (7 + 1) - 1)) (model_ln_wad_evm (2 ^ (7 + 1))) = true := by
  rw [ray_eval_seam_7_lo, ray_eval_seam_7_hi]
  unfold sle
  decide

private theorem wad_seam_7 :
    sle (model_ln_wad_to_wad_evm (2 ^ (7 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (7 + 1))) = true := by
  rw [wad_eval_seam_7_lo, wad_eval_seam_7_hi]
  unfold sle
  decide

private theorem ray_eval_seam_8_lo :
    model_ln_wad_evm (2 ^ (8 + 1) - 1) = 115792089237316195423570985008687907853269984665605353877373894890035003255352 := by
  have hlog : Nat.log2 (2 ^ (8 + 1) - 1) = 8 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (8 + 1) - 1) % 2 ^ 256 = 2 ^ (8 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_8_hi :
    model_ln_wad_evm (2 ^ (8 + 1)) = 115792089237316195423570985008687907853269984665605355832408730693385560882844 := by
  have hlog : Nat.log2 (2 ^ (8 + 1)) = 9 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (8 + 1)) % 2 ^ 256 = 2 ^ (8 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_8_lo :
    model_ln_wad_to_wad_evm (2 ^ (8 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039422373845829440522057 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (8 + 1) - 1) % 2 ^ 256 = 2 ^ (8 + 1) - 1 by decide]
  rw [ray_eval_seam_8_lo]
  decide

private theorem wad_eval_seam_8_hi :
    model_ln_wad_to_wad_evm (2 ^ (8 + 1)) = 115792089237316195423570985008687907853269984665640564039422375800864276325408 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (8 + 1)) % 2 ^ 256 = 2 ^ (8 + 1) by decide]
  rw [ray_eval_seam_8_hi]
  decide

private theorem ray_seam_8 :
    sle (model_ln_wad_evm (2 ^ (8 + 1) - 1)) (model_ln_wad_evm (2 ^ (8 + 1))) = true := by
  rw [ray_eval_seam_8_lo, ray_eval_seam_8_hi]
  unfold sle
  decide

private theorem wad_seam_8 :
    sle (model_ln_wad_to_wad_evm (2 ^ (8 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (8 + 1))) = true := by
  rw [wad_eval_seam_8_lo, wad_eval_seam_8_hi]
  unfold sle
  decide

private theorem ray_eval_seam_9_lo :
    model_ln_wad_evm (2 ^ (9 + 1) - 1) = 115792089237316195423570985008687907853269984665606048002549642812082192146890 := by
  have hlog : Nat.log2 (2 ^ (9 + 1) - 1) = 9 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (9 + 1) - 1) % 2 ^ 256 = 2 ^ (9 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_9_hi :
    model_ln_wad_evm (2 ^ (9 + 1)) = 115792089237316195423570985008687907853269984665606048979589290638694978114966 := by
  have hlog : Nat.log2 (2 ^ (9 + 1)) = 10 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (9 + 1)) % 2 ^ 256 = 2 ^ (9 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_9_lo :
    model_ln_wad_to_wad_evm (2 ^ (9 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039423067971005188444105 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (9 + 1) - 1) % 2 ^ 256 = 2 ^ (9 + 1) - 1 by decide]
  rw [ray_eval_seam_9_lo]
  decide

private theorem wad_eval_seam_9_hi :
    model_ln_wad_to_wad_evm (2 ^ (9 + 1)) = 115792089237316195423570985008687907853269984665640564039423068948044836270717 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (9 + 1)) % 2 ^ 256 = 2 ^ (9 + 1) by decide]
  rw [ray_eval_seam_9_hi]
  decide

private theorem ray_seam_9 :
    sle (model_ln_wad_evm (2 ^ (9 + 1) - 1)) (model_ln_wad_evm (2 ^ (9 + 1))) = true := by
  rw [ray_eval_seam_9_lo, ray_eval_seam_9_hi]
  unfold sle
  decide

private theorem wad_seam_9 :
    sle (model_ln_wad_to_wad_evm (2 ^ (9 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (9 + 1))) = true := by
  rw [wad_eval_seam_9_lo, wad_eval_seam_9_hi]
  unfold sle
  decide

private theorem ray_eval_seam_10_lo :
    model_ln_wad_evm (2 ^ (10 + 1) - 1) = 115792089237316195423570985008687907853269984665606741638369352475129930362123 := by
  have hlog : Nat.log2 (2 ^ (10 + 1) - 1) = 10 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (10 + 1) - 1) % 2 ^ 256 = 2 ^ (10 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_10_hi :
    model_ln_wad_evm (2 ^ (10 + 1)) = 115792089237316195423570985008687907853269984665606742126769850584004395347087 := by
  have hlog : Nat.log2 (2 ^ (10 + 1)) = 11 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (10 + 1)) % 2 ^ 256 = 2 ^ (10 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_10_lo :
    model_ln_wad_to_wad_evm (2 ^ (10 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039423761606824898107152 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (10 + 1) - 1) % 2 ^ 256 = 2 ^ (10 + 1) - 1 by decide]
  rw [ray_eval_seam_10_lo]
  decide

private theorem wad_eval_seam_10_hi :
    model_ln_wad_to_wad_evm (2 ^ (10 + 1)) = 115792089237316195423570985008687907853269984665640564039423762095225396216027 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (10 + 1)) % 2 ^ 256 = 2 ^ (10 + 1) by decide]
  rw [ray_eval_seam_10_hi]
  decide

private theorem ray_seam_10 :
    sle (model_ln_wad_evm (2 ^ (10 + 1) - 1)) (model_ln_wad_evm (2 ^ (10 + 1))) = true := by
  rw [ray_eval_seam_10_lo, ray_eval_seam_10_hi]
  unfold sle
  decide

private theorem wad_seam_10 :
    sle (model_ln_wad_to_wad_evm (2 ^ (10 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (10 + 1))) = true := by
  rw [wad_eval_seam_10_lo, wad_eval_seam_10_hi]
  unfold sle
  decide

private theorem ray_eval_seam_11_lo :
    model_ln_wad_evm (2 ^ (11 + 1) - 1) = 115792089237316195423570985008687907853269984665607435029779978355399355883743 := by
  have hlog : Nat.log2 (2 ^ (11 + 1) - 1) = 11 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (11 + 1) - 1) % 2 ^ 256 = 2 ^ (11 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_11_hi :
    model_ln_wad_evm (2 ^ (11 + 1)) = 115792089237316195423570985008687907853269984665607435273950410529313812579209 := by
  have hlog : Nat.log2 (2 ^ (11 + 1)) = 12 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (11 + 1)) % 2 ^ 256 = 2 ^ (11 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_11_lo :
    model_ln_wad_to_wad_evm (2 ^ (11 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039424454998235523987422 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (11 + 1) - 1) % 2 ^ 256 = 2 ^ (11 + 1) - 1 by decide]
  rw [ray_eval_seam_11_lo]
  decide

private theorem wad_eval_seam_11_hi :
    model_ln_wad_to_wad_evm (2 ^ (11 + 1)) = 115792089237316195423570985008687907853269984665640564039424455242405956161336 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (11 + 1)) % 2 ^ 256 = 2 ^ (11 + 1) by decide]
  rw [ray_eval_seam_11_hi]
  decide

private theorem ray_seam_11 :
    sle (model_ln_wad_evm (2 ^ (11 + 1) - 1)) (model_ln_wad_evm (2 ^ (11 + 1))) = true := by
  rw [ray_eval_seam_11_lo, ray_eval_seam_11_hi]
  unfold sle
  decide

private theorem wad_seam_11 :
    sle (model_ln_wad_to_wad_evm (2 ^ (11 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (11 + 1))) = true := by
  rw [wad_eval_seam_11_lo, wad_eval_seam_11_hi]
  unfold sle
  decide

private theorem ray_eval_seam_12_lo :
    model_ln_wad_evm (2 ^ (12 + 1) - 1) = 115792089237316195423570985008687907853269984665608128299053206787640988228459 := by
  have hlog : Nat.log2 (2 ^ (12 + 1) - 1) = 12 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (12 + 1) - 1) % 2 ^ 256 = 2 ^ (12 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_12_hi :
    model_ln_wad_evm (2 ^ (12 + 1)) = 115792089237316195423570985008687907853269984665608128421130970474623229811330 := by
  have hlog : Nat.log2 (2 ^ (12 + 1)) = 13 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (12 + 1)) % 2 ^ 256 = 2 ^ (12 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_12_lo :
    model_ln_wad_to_wad_evm (2 ^ (12 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039425148267508752419663 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (12 + 1) - 1) % 2 ^ 256 = 2 ^ (12 + 1) - 1 by decide]
  rw [ray_eval_seam_12_lo]
  decide

private theorem wad_eval_seam_12_hi :
    model_ln_wad_to_wad_evm (2 ^ (12 + 1)) = 115792089237316195423570985008687907853269984665640564039425148389586516106646 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (12 + 1)) % 2 ^ 256 = 2 ^ (12 + 1) by decide]
  rw [ray_eval_seam_12_hi]
  decide

private theorem ray_seam_12 :
    sle (model_ln_wad_evm (2 ^ (12 + 1) - 1)) (model_ln_wad_evm (2 ^ (12 + 1))) = true := by
  rw [ray_eval_seam_12_lo, ray_eval_seam_12_hi]
  unfold sle
  decide

private theorem wad_seam_12 :
    sle (model_ln_wad_to_wad_evm (2 ^ (12 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (12 + 1))) = true := by
  rw [wad_eval_seam_12_lo, wad_eval_seam_12_hi]
  unfold sle
  decide

private theorem ray_eval_seam_13_lo :
    model_ln_wad_evm (2 ^ (13 + 1) - 1) = 115792089237316195423570985008687907853269984665608821507274511448988721322309 := by
  have hlog : Nat.log2 (2 ^ (13 + 1) - 1) = 13 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (13 + 1) - 1) % 2 ^ 256 = 2 ^ (13 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_13_hi :
    model_ln_wad_evm (2 ^ (13 + 1)) = 115792089237316195423570985008687907853269984665608821568311530419932647043452 := by
  have hlog : Nat.log2 (2 ^ (13 + 1)) = 14 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (13 + 1)) % 2 ^ 256 = 2 ^ (13 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_13_lo :
    model_ln_wad_to_wad_evm (2 ^ (13 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039425841475730057081011 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (13 + 1) - 1) % 2 ^ 256 = 2 ^ (13 + 1) - 1 by decide]
  rw [ray_eval_seam_13_lo]
  decide

private theorem wad_eval_seam_13_hi :
    model_ln_wad_to_wad_evm (2 ^ (13 + 1)) = 115792089237316195423570985008687907853269984665640564039425841536767076051955 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (13 + 1)) % 2 ^ 256 = 2 ^ (13 + 1) by decide]
  rw [ray_eval_seam_13_hi]
  decide

private theorem ray_seam_13 :
    sle (model_ln_wad_evm (2 ^ (13 + 1) - 1)) (model_ln_wad_evm (2 ^ (13 + 1))) = true := by
  rw [ray_eval_seam_13_lo, ray_eval_seam_13_hi]
  unfold sle
  decide

private theorem wad_seam_13 :
    sle (model_ln_wad_to_wad_evm (2 ^ (13 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (13 + 1))) = true := by
  rw [wad_eval_seam_13_lo, wad_eval_seam_13_hi]
  unfold sle
  decide

private theorem ray_eval_seam_14_lo :
    model_ln_wad_evm (2 ^ (14 + 1) - 1) = 115792089237316195423570985008687907853269984665609514684974046569480636547118 := by
  have hlog : Nat.log2 (2 ^ (14 + 1) - 1) = 14 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (14 + 1) - 1) % 2 ^ 256 = 2 ^ (14 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_14_hi :
    model_ln_wad_evm (2 ^ (14 + 1)) = 115792089237316195423570985008687907853269984665609514715492090365242064275573 := by
  have hlog : Nat.log2 (2 ^ (14 + 1)) = 15 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (14 + 1)) % 2 ^ 256 = 2 ^ (14 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_14_lo :
    model_ln_wad_to_wad_evm (2 ^ (14 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039426534653429592201503 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (14 + 1) - 1) % 2 ^ 256 = 2 ^ (14 + 1) - 1 by decide]
  rw [ray_eval_seam_14_lo]
  decide

private theorem wad_eval_seam_14_hi :
    model_ln_wad_to_wad_evm (2 ^ (14 + 1)) = 115792089237316195423570985008687907853269984665640564039426534683947635997264 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (14 + 1)) % 2 ^ 256 = 2 ^ (14 + 1) by decide]
  rw [ray_eval_seam_14_hi]
  decide

private theorem ray_seam_14 :
    sle (model_ln_wad_evm (2 ^ (14 + 1) - 1)) (model_ln_wad_evm (2 ^ (14 + 1))) = true := by
  rw [ray_eval_seam_14_lo, ray_eval_seam_14_hi]
  unfold sle
  decide

private theorem wad_seam_14 :
    sle (model_ln_wad_to_wad_evm (2 ^ (14 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (14 + 1))) = true := by
  rw [wad_eval_seam_14_lo, wad_eval_seam_14_hi]
  unfold sle
  decide

private theorem ray_eval_seam_15_lo :
    model_ln_wad_evm (2 ^ (15 + 1) - 1) = 115792089237316195423570985008687907853269984665610207847413744831545403127253 := by
  have hlog : Nat.log2 (2 ^ (15 + 1) - 1) = 15 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (15 + 1) - 1) % 2 ^ 256 = 2 ^ (15 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_15_hi :
    model_ln_wad_evm (2 ^ (15 + 1)) = 115792089237316195423570985008687907853269984665610207862672650310551481507694 := by
  have hlog : Nat.log2 (2 ^ (15 + 1)) = 16 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (15 + 1)) % 2 ^ 256 = 2 ^ (15 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_15_lo :
    model_ln_wad_to_wad_evm (2 ^ (15 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039427227815869290463568 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (15 + 1) - 1) % 2 ^ 256 = 2 ^ (15 + 1) - 1 by decide]
  rw [ray_eval_seam_15_lo]
  decide

private theorem wad_eval_seam_15_hi :
    model_ln_wad_to_wad_evm (2 ^ (15 + 1)) = 115792089237316195423570985008687907853269984665640564039427227831128195942574 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (15 + 1)) % 2 ^ 256 = 2 ^ (15 + 1) by decide]
  rw [ray_eval_seam_15_hi]
  decide

private theorem ray_seam_15 :
    sle (model_ln_wad_evm (2 ^ (15 + 1) - 1)) (model_ln_wad_evm (2 ^ (15 + 1))) = true := by
  rw [ray_eval_seam_15_lo, ray_eval_seam_15_hi]
  unfold sle
  decide

private theorem wad_seam_15 :
    sle (model_ln_wad_to_wad_evm (2 ^ (15 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (15 + 1))) = true := by
  rw [wad_eval_seam_15_lo, wad_eval_seam_15_hi]
  unfold sle
  decide

private theorem ray_eval_seam_16_lo :
    model_ln_wad_evm (2 ^ (16 + 1) - 1) = 115792089237316195423570985008687907853269984665610901002223786620632411422457 := by
  have hlog : Nat.log2 (2 ^ (16 + 1) - 1) = 16 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (16 + 1) - 1) % 2 ^ 256 = 2 ^ (16 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_16_hi :
    model_ln_wad_evm (2 ^ (16 + 1)) = 115792089237316195423570985008687907853269984665610901009853210255860898739816 := by
  have hlog : Nat.log2 (2 ^ (16 + 1)) = 17 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (16 + 1)) % 2 ^ 256 = 2 ^ (16 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_16_lo :
    model_ln_wad_to_wad_evm (2 ^ (16 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039427920970679332252655 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (16 + 1) - 1) % 2 ^ 256 = 2 ^ (16 + 1) - 1 by decide]
  rw [ray_eval_seam_16_lo]
  decide

private theorem wad_eval_seam_16_hi :
    model_ln_wad_to_wad_evm (2 ^ (16 + 1)) = 115792089237316195423570985008687907853269984665640564039427920978308755887883 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (16 + 1)) % 2 ^ 256 = 2 ^ (16 + 1) by decide]
  rw [ray_eval_seam_16_hi]
  decide

private theorem ray_seam_16 :
    sle (model_ln_wad_evm (2 ^ (16 + 1) - 1)) (model_ln_wad_evm (2 ^ (16 + 1))) = true := by
  rw [ray_eval_seam_16_lo, ray_eval_seam_16_hi]
  unfold sle
  decide

private theorem wad_seam_16 :
    sle (model_ln_wad_to_wad_evm (2 ^ (16 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (16 + 1))) = true := by
  rw [wad_eval_seam_16_lo, wad_eval_seam_16_hi]
  unfold sle
  decide

private theorem ray_eval_seam_17_lo :
    model_ln_wad_evm (2 ^ (17 + 1) - 1) = 115792089237316195423570985008687907853269984665611594153219065659569198018494 := by
  have hlog : Nat.log2 (2 ^ (17 + 1) - 1) = 17 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (17 + 1) - 1) % 2 ^ 256 = 2 ^ (17 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_17_hi :
    model_ln_wad_evm (2 ^ (17 + 1)) = 115792089237316195423570985008687907853269984665611594157033770201170315971937 := by
  have hlog : Nat.log2 (2 ^ (17 + 1)) = 18 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (17 + 1)) % 2 ^ 256 = 2 ^ (17 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_17_lo :
    model_ln_wad_to_wad_evm (2 ^ (17 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039428614121674611291592 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (17 + 1) - 1) % 2 ^ 256 = 2 ^ (17 + 1) - 1 by decide]
  rw [ray_eval_seam_17_lo]
  decide

private theorem wad_eval_seam_17_hi :
    model_ln_wad_to_wad_evm (2 ^ (17 + 1)) = 115792089237316195423570985008687907853269984665640564039428614125489315833193 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (17 + 1)) % 2 ^ 256 = 2 ^ (17 + 1) by decide]
  rw [ray_eval_seam_17_hi]
  decide

private theorem ray_seam_17 :
    sle (model_ln_wad_evm (2 ^ (17 + 1) - 1)) (model_ln_wad_evm (2 ^ (17 + 1))) = true := by
  rw [ray_eval_seam_17_lo, ray_eval_seam_17_hi]
  unfold sle
  decide

private theorem wad_seam_17 :
    sle (model_ln_wad_to_wad_evm (2 ^ (17 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (17 + 1))) = true := by
  rw [wad_eval_seam_17_lo, wad_eval_seam_17_hi]
  unfold sle
  decide

private theorem ray_eval_seam_18_lo :
    model_ln_wad_evm (2 ^ (18 + 1) - 1) = 115792089237316195423570985008687907853269984665612287302306979694675516690258 := by
  have hlog : Nat.log2 (2 ^ (18 + 1) - 1) = 18 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (18 + 1) - 1) % 2 ^ 256 = 2 ^ (18 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_18_hi :
    model_ln_wad_evm (2 ^ (18 + 1)) = 115792089237316195423570985008687907853269984665612287304214330146479733204059 := by
  have hlog : Nat.log2 (2 ^ (18 + 1)) = 19 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (18 + 1)) % 2 ^ 256 = 2 ^ (18 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_18_lo :
    model_ln_wad_to_wad_evm (2 ^ (18 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039429307270762525326698 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (18 + 1) - 1) % 2 ^ 256 = 2 ^ (18 + 1) - 1 by decide]
  rw [ray_eval_seam_18_lo]
  decide

private theorem wad_eval_seam_18_hi :
    model_ln_wad_to_wad_evm (2 ^ (18 + 1)) = 115792089237316195423570985008687907853269984665640564039429307272669875778502 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (18 + 1)) % 2 ^ 256 = 2 ^ (18 + 1) by decide]
  rw [ray_eval_seam_18_hi]
  decide

private theorem ray_seam_18 :
    sle (model_ln_wad_evm (2 ^ (18 + 1) - 1)) (model_ln_wad_evm (2 ^ (18 + 1))) = true := by
  rw [ray_eval_seam_18_lo, ray_eval_seam_18_hi]
  unfold sle
  decide

private theorem wad_seam_18 :
    sle (model_ln_wad_to_wad_evm (2 ^ (18 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (18 + 1))) = true := by
  rw [wad_eval_seam_18_lo, wad_eval_seam_18_hi]
  unfold sle
  decide

private theorem ray_eval_seam_19_lo :
    model_ln_wad_evm (2 ^ (19 + 1) - 1) = 115792089237316195423570985008687907853269984665612980450441215320635260428929 := by
  have hlog : Nat.log2 (2 ^ (19 + 1) - 1) = 19 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (19 + 1) - 1) % 2 ^ 256 = 2 ^ (19 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_19_hi :
    model_ln_wad_evm (2 ^ (19 + 1)) = 115792089237316195423570985008687907853269984665612980451394890091789150436180 := by
  have hlog : Nat.log2 (2 ^ (19 + 1)) = 20 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (19 + 1)) % 2 ^ 256 = 2 ^ (19 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_19_lo :
    model_ln_wad_to_wad_evm (2 ^ (19 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039430000418896760952658 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (19 + 1) - 1) % 2 ^ 256 = 2 ^ (19 + 1) - 1 by decide]
  rw [ray_eval_seam_19_lo]
  decide

private theorem wad_eval_seam_19_hi :
    model_ln_wad_to_wad_evm (2 ^ (19 + 1)) = 115792089237316195423570985008687907853269984665640564039430000419850435723812 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (19 + 1)) % 2 ^ 256 = 2 ^ (19 + 1) by decide]
  rw [ray_eval_seam_19_hi]
  decide

private theorem ray_seam_19 :
    sle (model_ln_wad_evm (2 ^ (19 + 1) - 1)) (model_ln_wad_evm (2 ^ (19 + 1))) = true := by
  rw [ray_eval_seam_19_lo, ray_eval_seam_19_hi]
  unfold sle
  decide

private theorem wad_seam_19 :
    sle (model_ln_wad_to_wad_evm (2 ^ (19 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (19 + 1))) = true := by
  rw [wad_eval_seam_19_lo, wad_eval_seam_19_hi]
  unfold sle
  decide

private theorem ray_eval_seam_20_lo :
    model_ln_wad_evm (2 ^ (20 + 1) - 1) = 115792089237316195423570985008687907853269984665613673598098612765208568806600 := by
  have hlog : Nat.log2 (2 ^ (20 + 1) - 1) = 20 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (20 + 1) - 1) % 2 ^ 256 = 2 ^ (20 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_20_hi :
    model_ln_wad_evm (2 ^ (20 + 1)) = 115792089237316195423570985008687907853269984665613673598575450037098567668302 := by
  have hlog : Nat.log2 (2 ^ (20 + 1)) = 21 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (20 + 1)) % 2 ^ 256 = 2 ^ (20 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_20_lo :
    model_ln_wad_to_wad_evm (2 ^ (20 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039430693566554158397231 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (20 + 1) - 1) % 2 ^ 256 = 2 ^ (20 + 1) - 1 by decide]
  rw [ray_eval_seam_20_lo]
  decide

private theorem wad_eval_seam_20_hi :
    model_ln_wad_to_wad_evm (2 ^ (20 + 1)) = 115792089237316195423570985008687907853269984665640564039430693567030995669121 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (20 + 1)) % 2 ^ 256 = 2 ^ (20 + 1) by decide]
  rw [ray_eval_seam_20_hi]
  decide

private theorem ray_seam_20 :
    sle (model_ln_wad_evm (2 ^ (20 + 1) - 1)) (model_ln_wad_evm (2 ^ (20 + 1))) = true := by
  rw [ray_eval_seam_20_lo, ray_eval_seam_20_hi]
  unfold sle
  decide

private theorem wad_seam_20 :
    sle (model_ln_wad_to_wad_evm (2 ^ (20 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (20 + 1))) = true := by
  rw [wad_eval_seam_20_lo, wad_eval_seam_20_hi]
  unfold sle
  decide

private theorem ray_eval_seam_21_lo :
    model_ln_wad_evm (2 ^ (21 + 1) - 1) = 115792089237316195423570985008687907853269984665614366745517591374884708452509 := by
  have hlog : Nat.log2 (2 ^ (21 + 1) - 1) = 21 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (21 + 1) - 1) % 2 ^ 256 = 2 ^ (21 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_21_hi :
    model_ln_wad_evm (2 ^ (21 + 1)) = 115792089237316195423570985008687907853269984665614366745756009982407984900423 := by
  have hlog : Nat.log2 (2 ^ (21 + 1)) = 22 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (21 + 1)) % 2 ^ 256 = 2 ^ (21 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_21_lo :
    model_ln_wad_to_wad_evm (2 ^ (21 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039431386713973137006907 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (21 + 1) - 1) % 2 ^ 256 = 2 ^ (21 + 1) - 1 by decide]
  rw [ray_eval_seam_21_lo]
  decide

private theorem wad_eval_seam_21_hi :
    model_ln_wad_to_wad_evm (2 ^ (21 + 1)) = 115792089237316195423570985008687907853269984665640564039431386714211555614430 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (21 + 1)) % 2 ^ 256 = 2 ^ (21 + 1) by decide]
  rw [ray_eval_seam_21_hi]
  decide

private theorem ray_seam_21 :
    sle (model_ln_wad_evm (2 ^ (21 + 1) - 1)) (model_ln_wad_evm (2 ^ (21 + 1))) = true := by
  rw [ray_eval_seam_21_lo, ray_eval_seam_21_hi]
  unfold sle
  decide

private theorem wad_seam_21 :
    sle (model_ln_wad_to_wad_evm (2 ^ (21 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (21 + 1))) = true := by
  rw [wad_eval_seam_21_lo, wad_eval_seam_21_hi]
  unfold sle
  decide

private theorem ray_eval_seam_22_lo :
    model_ln_wad_evm (2 ^ (22 + 1) - 1) = 115792089237316195423570985008687907853269984665615059892817360631061192960254 := by
  have hlog : Nat.log2 (2 ^ (22 + 1) - 1) = 22 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (22 + 1) - 1) % 2 ^ 256 = 2 ^ (22 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_22_hi :
    model_ln_wad_evm (2 ^ (22 + 1)) = 115792089237316195423570985008687907853269984665615059892936569927717402132545 := by
  have hlog : Nat.log2 (2 ^ (22 + 1)) = 23 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (22 + 1)) % 2 ^ 256 = 2 ^ (22 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_22_lo :
    model_ln_wad_to_wad_evm (2 ^ (22 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039432079861272906263084 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (22 + 1) - 1) % 2 ^ 256 = 2 ^ (22 + 1) - 1 by decide]
  rw [ray_eval_seam_22_lo]
  decide

private theorem wad_eval_seam_22_hi :
    model_ln_wad_to_wad_evm (2 ^ (22 + 1)) = 115792089237316195423570985008687907853269984665640564039432079861392115559740 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (22 + 1)) % 2 ^ 256 = 2 ^ (22 + 1) by decide]
  rw [ray_eval_seam_22_hi]
  decide

private theorem ray_seam_22 :
    sle (model_ln_wad_evm (2 ^ (22 + 1) - 1)) (model_ln_wad_evm (2 ^ (22 + 1))) = true := by
  rw [ray_eval_seam_22_lo, ray_eval_seam_22_hi]
  unfold sle
  decide

private theorem wad_seam_22 :
    sle (model_ln_wad_to_wad_evm (2 ^ (22 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (22 + 1))) = true := by
  rw [wad_eval_seam_22_lo, wad_eval_seam_22_hi]
  unfold sle
  decide

private theorem ray_eval_seam_23_lo :
    model_ln_wad_evm (2 ^ (23 + 1) - 1) = 115792089237316195423570985008687907853269984665615753040057525226475071829679 := by
  have hlog : Nat.log2 (2 ^ (23 + 1) - 1) = 23 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (23 + 1) - 1) % 2 ^ 256 = 2 ^ (23 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_23_hi :
    model_ln_wad_evm (2 ^ (23 + 1)) = 115792089237316195423570985008687907853269984665615753040117129873026819364666 := by
  have hlog : Nat.log2 (2 ^ (23 + 1)) = 24 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (23 + 1)) % 2 ^ 256 = 2 ^ (23 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_23_lo :
    model_ln_wad_to_wad_evm (2 ^ (23 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039432773008513070858497 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (23 + 1) - 1) % 2 ^ 256 = 2 ^ (23 + 1) - 1 by decide]
  rw [ray_eval_seam_23_lo]
  decide

private theorem wad_eval_seam_23_hi :
    model_ln_wad_to_wad_evm (2 ^ (23 + 1)) = 115792089237316195423570985008687907853269984665640564039432773008572675505049 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (23 + 1)) % 2 ^ 256 = 2 ^ (23 + 1) by decide]
  rw [ray_eval_seam_23_hi]
  decide

private theorem ray_seam_23 :
    sle (model_ln_wad_evm (2 ^ (23 + 1) - 1)) (model_ln_wad_evm (2 ^ (23 + 1))) = true := by
  rw [ray_eval_seam_23_lo, ray_eval_seam_23_hi]
  unfold sle
  decide

private theorem wad_seam_23 :
    sle (model_ln_wad_to_wad_evm (2 ^ (23 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (23 + 1))) = true := by
  rw [wad_eval_seam_23_lo, wad_eval_seam_23_hi]
  unfold sle
  decide

private theorem ray_eval_seam_24_lo :
    model_ln_wad_evm (2 ^ (24 + 1) - 1) = 115792089237316195423570985008687907853269984665616446187267887495504452065614 := by
  have hlog : Nat.log2 (2 ^ (24 + 1) - 1) = 24 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (24 + 1) - 1) % 2 ^ 256 = 2 ^ (24 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_24_hi :
    model_ln_wad_evm (2 ^ (24 + 1)) = 115792089237316195423570985008687907853269984665616446187297689818336236596788 := by
  have hlog : Nat.log2 (2 ^ (24 + 1)) = 25 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (24 + 1)) % 2 ^ 256 = 2 ^ (24 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_24_lo :
    model_ln_wad_to_wad_evm (2 ^ (24 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039433466155723433127527 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (24 + 1) - 1) % 2 ^ 256 = 2 ^ (24 + 1) - 1 by decide]
  rw [ray_eval_seam_24_lo]
  decide

private theorem wad_eval_seam_24_hi :
    model_ln_wad_to_wad_evm (2 ^ (24 + 1)) = 115792089237316195423570985008687907853269984665640564039433466155753235450359 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (24 + 1)) % 2 ^ 256 = 2 ^ (24 + 1) by decide]
  rw [ray_eval_seam_24_hi]
  decide

private theorem ray_seam_24 :
    sle (model_ln_wad_evm (2 ^ (24 + 1) - 1)) (model_ln_wad_evm (2 ^ (24 + 1))) = true := by
  rw [ray_eval_seam_24_lo, ray_eval_seam_24_hi]
  unfold sle
  decide

private theorem wad_seam_24 :
    sle (model_ln_wad_to_wad_evm (2 ^ (24 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (24 + 1))) = true := by
  rw [wad_eval_seam_24_lo, wad_eval_seam_24_hi]
  unfold sle
  decide

private theorem ray_eval_seam_25_lo :
    model_ln_wad_evm (2 ^ (25 + 1) - 1) = 115792089237316195423570985008687907853269984665617139334463348602340783869093 := by
  have hlog : Nat.log2 (2 ^ (25 + 1) - 1) = 25 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (25 + 1) - 1) % 2 ^ 256 = 2 ^ (25 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_25_hi :
    model_ln_wad_evm (2 ^ (25 + 1)) = 115792089237316195423570985008687907853269984665617139334478249763645653828909 := by
  have hlog : Nat.log2 (2 ^ (25 + 1)) = 26 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (25 + 1)) % 2 ^ 256 = 2 ^ (25 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_25_lo :
    model_ln_wad_to_wad_evm (2 ^ (25 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039434159302918894234363 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (25 + 1) - 1) % 2 ^ 256 = 2 ^ (25 + 1) - 1 by decide]
  rw [ray_eval_seam_25_lo]
  decide

private theorem wad_eval_seam_25_hi :
    model_ln_wad_to_wad_evm (2 ^ (25 + 1)) = 115792089237316195423570985008687907853269984665640564039434159302933795395668 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (25 + 1)) % 2 ^ 256 = 2 ^ (25 + 1) by decide]
  rw [ray_eval_seam_25_hi]
  decide

private theorem ray_seam_25 :
    sle (model_ln_wad_evm (2 ^ (25 + 1) - 1)) (model_ln_wad_evm (2 ^ (25 + 1))) = true := by
  rw [ray_eval_seam_25_lo, ray_eval_seam_25_hi]
  unfold sle
  decide

private theorem wad_seam_25 :
    sle (model_ln_wad_to_wad_evm (2 ^ (25 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (25 + 1))) = true := by
  rw [wad_eval_seam_25_lo, wad_eval_seam_25_hi]
  unfold sle
  decide

private theorem ray_eval_seam_26_lo :
    model_ln_wad_evm (2 ^ (26 + 1) - 1) = 115792089237316195423570985008687907853269984665617832481651359128330391657151 := by
  have hlog : Nat.log2 (2 ^ (26 + 1) - 1) = 26 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (26 + 1) - 1) % 2 ^ 256 = 2 ^ (26 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_26_hi :
    model_ln_wad_evm (2 ^ (26 + 1)) = 115792089237316195423570985008687907853269984665617832481658809708955071061031 := by
  have hlog : Nat.log2 (2 ^ (26 + 1)) = 27 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (26 + 1)) % 2 ^ 256 = 2 ^ (26 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_26_lo :
    model_ln_wad_to_wad_evm (2 ^ (26 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039434852450106904760353 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (26 + 1) - 1) % 2 ^ 256 = 2 ^ (26 + 1) - 1 by decide]
  rw [ray_eval_seam_26_lo]
  decide

private theorem wad_eval_seam_26_hi :
    model_ln_wad_to_wad_evm (2 ^ (26 + 1)) = 115792089237316195423570985008687907853269984665640564039434852450114355340977 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (26 + 1)) % 2 ^ 256 = 2 ^ (26 + 1) by decide]
  rw [ray_eval_seam_26_hi]
  decide

private theorem ray_seam_26 :
    sle (model_ln_wad_evm (2 ^ (26 + 1) - 1)) (model_ln_wad_evm (2 ^ (26 + 1))) = true := by
  rw [ray_eval_seam_26_lo, ray_eval_seam_26_hi]
  unfold sle
  decide

private theorem wad_seam_26 :
    sle (model_ln_wad_to_wad_evm (2 ^ (26 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (26 + 1))) = true := by
  rw [wad_eval_seam_26_lo, wad_eval_seam_26_hi]
  unfold sle
  decide

private theorem ray_eval_seam_27_lo :
    model_ln_wad_evm (2 ^ (27 + 1) - 1) = 115792089237316195423570985008687907853269984665618525628835644363959087485168 := by
  have hlog : Nat.log2 (2 ^ (27 + 1) - 1) = 27 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (27 + 1) - 1) % 2 ^ 256 = 2 ^ (27 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_27_hi :
    model_ln_wad_evm (2 ^ (27 + 1)) = 115792089237316195423570985008687907853269984665618525628839369654264488293152 := by
  have hlog : Nat.log2 (2 ^ (27 + 1)) = 28 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (27 + 1)) % 2 ^ 256 = 2 ^ (27 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_27_lo :
    model_ln_wad_to_wad_evm (2 ^ (27 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039435545597291189995981 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (27 + 1) - 1) % 2 ^ 256 = 2 ^ (27 + 1) - 1 by decide]
  rw [ray_eval_seam_27_lo]
  decide

private theorem wad_eval_seam_27_hi :
    model_ln_wad_to_wad_evm (2 ^ (27 + 1)) = 115792089237316195423570985008687907853269984665640564039435545597294915286287 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (27 + 1)) % 2 ^ 256 = 2 ^ (27 + 1) by decide]
  rw [ray_eval_seam_27_hi]
  decide

private theorem ray_seam_27 :
    sle (model_ln_wad_evm (2 ^ (27 + 1) - 1)) (model_ln_wad_evm (2 ^ (27 + 1))) = true := by
  rw [ray_eval_seam_27_lo, ray_eval_seam_27_hi]
  unfold sle
  decide

private theorem wad_seam_27 :
    sle (model_ln_wad_to_wad_evm (2 ^ (27 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (27 + 1))) = true := by
  rw [wad_eval_seam_27_lo, wad_eval_seam_27_hi]
  unfold sle
  decide

private theorem ray_eval_seam_28_lo :
    model_ln_wad_evm (2 ^ (28 + 1) - 1) = 115792089237316195423570985008687907853269984665619218776018066954422939844763 := by
  have hlog : Nat.log2 (2 ^ (28 + 1) - 1) = 28 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (28 + 1) - 1) % 2 ^ 256 = 2 ^ (28 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_28_hi :
    model_ln_wad_evm (2 ^ (28 + 1)) = 115792089237316195423570985008687907853269984665619218776019929599573905525273 := by
  have hlog : Nat.log2 (2 ^ (28 + 1)) = 29 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (28 + 1)) % 2 ^ 256 = 2 ^ (28 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_28_lo :
    model_ln_wad_to_wad_evm (2 ^ (28 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039436238744473612586445 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (28 + 1) - 1) % 2 ^ 256 = 2 ^ (28 + 1) - 1 by decide]
  rw [ray_eval_seam_28_lo]
  decide

private theorem wad_eval_seam_28_hi :
    model_ln_wad_to_wad_evm (2 ^ (28 + 1)) = 115792089237316195423570985008687907853269984665640564039436238744475475231596 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (28 + 1)) % 2 ^ 256 = 2 ^ (28 + 1) by decide]
  rw [ray_eval_seam_28_hi]
  decide

private theorem ray_seam_28 :
    sle (model_ln_wad_evm (2 ^ (28 + 1) - 1)) (model_ln_wad_evm (2 ^ (28 + 1))) = true := by
  rw [ray_eval_seam_28_lo, ray_eval_seam_28_hi]
  unfold sle
  decide

private theorem wad_seam_28 :
    sle (model_ln_wad_to_wad_evm (2 ^ (28 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (28 + 1))) = true := by
  rw [wad_eval_seam_28_lo, wad_eval_seam_28_hi]
  unfold sle
  decide

private theorem ray_eval_seam_29_lo :
    model_ln_wad_evm (2 ^ (29 + 1) - 1) = 115792089237316195423570985008687907853269984665619911923199558222308273598009 := by
  have hlog : Nat.log2 (2 ^ (29 + 1) - 1) = 29 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (29 + 1) - 1) % 2 ^ 256 = 2 ^ (29 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_29_hi :
    model_ln_wad_evm (2 ^ (29 + 1)) = 115792089237316195423570985008687907853269984665619911923200489544883322757395 := by
  have hlog : Nat.log2 (2 ^ (29 + 1)) = 30 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (29 + 1)) % 2 ^ 256 = 2 ^ (29 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_29_lo :
    model_ln_wad_to_wad_evm (2 ^ (29 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039436931891655103854331 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (29 + 1) - 1) % 2 ^ 256 = 2 ^ (29 + 1) - 1 by decide]
  rw [ray_eval_seam_29_lo]
  decide

private theorem wad_eval_seam_29_hi :
    model_ln_wad_to_wad_evm (2 ^ (29 + 1)) = 115792089237316195423570985008687907853269984665640564039436931891656035176906 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (29 + 1)) % 2 ^ 256 = 2 ^ (29 + 1) by decide]
  rw [ray_eval_seam_29_hi]
  decide

private theorem ray_seam_29 :
    sle (model_ln_wad_evm (2 ^ (29 + 1) - 1)) (model_ln_wad_evm (2 ^ (29 + 1))) = true := by
  rw [ray_eval_seam_29_lo, ray_eval_seam_29_hi]
  unfold sle
  decide

private theorem wad_seam_29 :
    sle (model_ln_wad_to_wad_evm (2 ^ (29 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (29 + 1))) = true := by
  rw [wad_eval_seam_29_lo, wad_eval_seam_29_hi]
  unfold sle
  decide

private theorem ray_eval_seam_30_lo :
    model_ln_wad_evm (2 ^ (30 + 1) - 1) = 115792089237316195423570985008687907853269984665620605070380583828905323830041 := by
  have hlog : Nat.log2 (2 ^ (30 + 1) - 1) = 30 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (30 + 1) - 1) % 2 ^ 256 = 2 ^ (30 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_30_hi :
    model_ln_wad_evm (2 ^ (30 + 1)) = 115792089237316195423570985008687907853269984665620605070381049490192739989516 := by
  have hlog : Nat.log2 (2 ^ (30 + 1)) = 31 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (30 + 1)) % 2 ^ 256 = 2 ^ (30 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_30_lo :
    model_ln_wad_to_wad_evm (2 ^ (30 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039437625038836129460928 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (30 + 1) - 1) % 2 ^ 256 = 2 ^ (30 + 1) - 1 by decide]
  rw [ray_eval_seam_30_lo]
  decide

private theorem wad_eval_seam_30_hi :
    model_ln_wad_to_wad_evm (2 ^ (30 + 1)) = 115792089237316195423570985008687907853269984665640564039437625038836595122215 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (30 + 1)) % 2 ^ 256 = 2 ^ (30 + 1) by decide]
  rw [ray_eval_seam_30_hi]
  decide

private theorem ray_seam_30 :
    sle (model_ln_wad_evm (2 ^ (30 + 1) - 1)) (model_ln_wad_evm (2 ^ (30 + 1))) = true := by
  rw [ray_eval_seam_30_lo, ray_eval_seam_30_hi]
  unfold sle
  decide

private theorem wad_seam_30 :
    sle (model_ln_wad_to_wad_evm (2 ^ (30 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (30 + 1))) = true := by
  rw [wad_eval_seam_30_lo, wad_eval_seam_30_hi]
  unfold sle
  decide

private theorem ray_eval_seam_31_lo :
    model_ln_wad_evm (2 ^ (31 + 1) - 1) = 115792089237316195423570985008687907853269984665621298217561376604858476246954 := by
  have hlog : Nat.log2 (2 ^ (31 + 1) - 1) = 31 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (31 + 1) - 1) % 2 ^ 256 = 2 ^ (31 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_31_hi :
    model_ln_wad_evm (2 ^ (31 + 1)) = 115792089237316195423570985008687907853269984665621298217561609435502157221638 := by
  have hlog : Nat.log2 (2 ^ (31 + 1)) = 32 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (31 + 1)) % 2 ^ 256 = 2 ^ (31 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_31_lo :
    model_ln_wad_to_wad_evm (2 ^ (31 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039438318186016922236881 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (31 + 1) - 1) % 2 ^ 256 = 2 ^ (31 + 1) - 1 by decide]
  rw [ray_eval_seam_31_lo]
  decide

private theorem wad_eval_seam_31_hi :
    model_ln_wad_to_wad_evm (2 ^ (31 + 1)) = 115792089237316195423570985008687907853269984665640564039438318186017155067525 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (31 + 1)) % 2 ^ 256 = 2 ^ (31 + 1) by decide]
  rw [ray_eval_seam_31_hi]
  decide

private theorem ray_seam_31 :
    sle (model_ln_wad_evm (2 ^ (31 + 1) - 1)) (model_ln_wad_evm (2 ^ (31 + 1))) = true := by
  rw [ray_eval_seam_31_lo, ray_eval_seam_31_hi]
  unfold sle
  decide

private theorem wad_seam_31 :
    sle (model_ln_wad_to_wad_evm (2 ^ (31 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (31 + 1))) = true := by
  rw [wad_eval_seam_31_lo, wad_eval_seam_31_hi]
  unfold sle
  decide

private theorem ray_eval_seam_32_lo :
    model_ln_wad_evm (2 ^ (32 + 1) - 1) = 115792089237316195423570985008687907853269984665621991364742052965489740742681 := by
  have hlog : Nat.log2 (2 ^ (32 + 1) - 1) = 32 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (32 + 1) - 1) % 2 ^ 256 = 2 ^ (32 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_32_hi :
    model_ln_wad_evm (2 ^ (32 + 1)) = 115792089237316195423570985008687907853269984665621991364742169380811574453759 := by
  have hlog : Nat.log2 (2 ^ (32 + 1)) = 33 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (32 + 1)) % 2 ^ 256 = 2 ^ (32 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_32_lo :
    model_ln_wad_to_wad_evm (2 ^ (32 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039439011333197598597512 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (32 + 1) - 1) % 2 ^ 256 = 2 ^ (32 + 1) - 1 by decide]
  rw [ray_eval_seam_32_lo]
  decide

private theorem wad_eval_seam_32_hi :
    model_ln_wad_to_wad_evm (2 ^ (32 + 1)) = 115792089237316195423570985008687907853269984665640564039439011333197715012834 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (32 + 1)) % 2 ^ 256 = 2 ^ (32 + 1) by decide]
  rw [ray_eval_seam_32_hi]
  decide

private theorem ray_seam_32 :
    sle (model_ln_wad_evm (2 ^ (32 + 1) - 1)) (model_ln_wad_evm (2 ^ (32 + 1))) = true := by
  rw [ray_eval_seam_32_lo, ray_eval_seam_32_hi]
  unfold sle
  decide

private theorem wad_seam_32 :
    sle (model_ln_wad_to_wad_evm (2 ^ (32 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (32 + 1))) = true := by
  rw [wad_eval_seam_32_lo, wad_eval_seam_32_hi]
  unfold sle
  decide

private theorem ray_eval_seam_33_lo :
    model_ln_wad_evm (2 ^ (33 + 1) - 1) = 115792089237316195423570985008687907853269984665622684511922671118460076524407 := by
  have hlog : Nat.log2 (2 ^ (33 + 1) - 1) = 33 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (33 + 1) - 1) % 2 ^ 256 = 2 ^ (33 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_33_hi :
    model_ln_wad_evm (2 ^ (33 + 1)) = 115792089237316195423570985008687907853269984665622684511922729326120991685881 := by
  have hlog : Nat.log2 (2 ^ (33 + 1)) = 34 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (33 + 1)) % 2 ^ 256 = 2 ^ (33 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_33_lo :
    model_ln_wad_to_wad_evm (2 ^ (33 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039439704480378216750482 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (33 + 1) - 1) % 2 ^ 256 = 2 ^ (33 + 1) - 1 by decide]
  rw [ray_eval_seam_33_lo]
  decide

private theorem wad_eval_seam_33_hi :
    model_ln_wad_to_wad_evm (2 ^ (33 + 1)) = 115792089237316195423570985008687907853269984665640564039439704480378274958143 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (33 + 1)) % 2 ^ 256 = 2 ^ (33 + 1) by decide]
  rw [ray_eval_seam_33_hi]
  decide

private theorem ray_seam_33 :
    sle (model_ln_wad_evm (2 ^ (33 + 1) - 1)) (model_ln_wad_evm (2 ^ (33 + 1))) = true := by
  rw [ray_eval_seam_33_lo, ray_eval_seam_33_hi]
  unfold sle
  decide

private theorem wad_seam_33 :
    sle (model_ln_wad_to_wad_evm (2 ^ (33 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (33 + 1))) = true := by
  rw [wad_eval_seam_33_lo, wad_eval_seam_33_hi]
  unfold sle
  decide

private theorem ray_eval_seam_34_lo :
    model_ln_wad_evm (2 ^ (34 + 1) - 1) = 115792089237316195423570985008687907853269984665623377659103260167599951760781 := by
  have hlog : Nat.log2 (2 ^ (34 + 1) - 1) = 34 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (34 + 1) - 1) % 2 ^ 256 = 2 ^ (34 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_34_hi :
    model_ln_wad_evm (2 ^ (34 + 1)) = 115792089237316195423570985008687907853269984665623377659103289271430408918002 := by
  have hlog : Nat.log2 (2 ^ (34 + 1)) = 35 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (34 + 1)) % 2 ^ 256 = 2 ^ (34 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_34_lo :
    model_ln_wad_to_wad_evm (2 ^ (34 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039440397627558805799622 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (34 + 1) - 1) % 2 ^ 256 = 2 ^ (34 + 1) - 1 by decide]
  rw [ray_eval_seam_34_lo]
  decide

private theorem wad_eval_seam_34_hi :
    model_ln_wad_to_wad_evm (2 ^ (34 + 1)) = 115792089237316195423570985008687907853269984665640564039440397627558834903453 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (34 + 1)) % 2 ^ 256 = 2 ^ (34 + 1) by decide]
  rw [ray_eval_seam_34_hi]
  decide

private theorem ray_seam_34 :
    sle (model_ln_wad_evm (2 ^ (34 + 1) - 1)) (model_ln_wad_evm (2 ^ (34 + 1))) = true := by
  rw [ray_eval_seam_34_lo, ray_eval_seam_34_hi]
  unfold sle
  decide

private theorem wad_seam_34 :
    sle (model_ln_wad_to_wad_evm (2 ^ (34 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (34 + 1))) = true := by
  rw [wad_eval_seam_34_lo, wad_eval_seam_34_hi]
  unfold sle
  decide

private theorem ray_eval_seam_35_lo :
    model_ln_wad_evm (2 ^ (35 + 1) - 1) = 115792089237316195423570985008687907853269984665624070806283834664824597677392 := by
  have hlog : Nat.log2 (2 ^ (35 + 1) - 1) = 35 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (35 + 1) - 1) % 2 ^ 256 = 2 ^ (35 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_35_hi :
    model_ln_wad_evm (2 ^ (35 + 1)) = 115792089237316195423570985008687907853269984665624070806283849216739826150124 := by
  have hlog : Nat.log2 (2 ^ (35 + 1)) = 36 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (35 + 1)) % 2 ^ 256 = 2 ^ (35 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_35_lo :
    model_ln_wad_to_wad_evm (2 ^ (35 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039441090774739380296847 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (35 + 1) - 1) % 2 ^ 256 = 2 ^ (35 + 1) - 1 by decide]
  rw [ray_eval_seam_35_lo]
  decide

private theorem wad_eval_seam_35_hi :
    model_ln_wad_to_wad_evm (2 ^ (35 + 1)) = 115792089237316195423570985008687907853269984665640564039441090774739394848762 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (35 + 1)) % 2 ^ 256 = 2 ^ (35 + 1) by decide]
  rw [ray_eval_seam_35_hi]
  decide

private theorem ray_seam_35 :
    sle (model_ln_wad_evm (2 ^ (35 + 1) - 1)) (model_ln_wad_evm (2 ^ (35 + 1))) = true := by
  rw [ray_eval_seam_35_lo, ray_eval_seam_35_hi]
  unfold sle
  decide

private theorem wad_seam_35 :
    sle (model_ln_wad_to_wad_evm (2 ^ (35 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (35 + 1))) = true := by
  rw [wad_eval_seam_35_lo, wad_eval_seam_35_hi]
  unfold sle
  decide

private theorem ray_eval_seam_36_lo :
    model_ln_wad_evm (2 ^ (36 + 1) - 1) = 115792089237316195423570985008687907853269984665624763953464401886091629172349 := by
  have hlog : Nat.log2 (2 ^ (36 + 1) - 1) = 36 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (36 + 1) - 1) % 2 ^ 256 = 2 ^ (36 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_36_hi :
    model_ln_wad_evm (2 ^ (36 + 1)) = 115792089237316195423570985008687907853269984665624763953464409162049243382245 := by
  have hlog : Nat.log2 (2 ^ (36 + 1)) = 37 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (36 + 1)) % 2 ^ 256 = 2 ^ (36 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_36_lo :
    model_ln_wad_to_wad_evm (2 ^ (36 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039441783921919947518114 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (36 + 1) - 1) % 2 ^ 256 = 2 ^ (36 + 1) - 1 by decide]
  rw [ray_eval_seam_36_lo]
  decide

private theorem wad_eval_seam_36_hi :
    model_ln_wad_to_wad_evm (2 ^ (36 + 1)) = 115792089237316195423570985008687907853269984665640564039441783921919954794072 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (36 + 1)) % 2 ^ 256 = 2 ^ (36 + 1) by decide]
  rw [ray_eval_seam_36_hi]
  decide

private theorem ray_seam_36 :
    sle (model_ln_wad_evm (2 ^ (36 + 1) - 1)) (model_ln_wad_evm (2 ^ (36 + 1))) = true := by
  rw [ray_eval_seam_36_lo, ray_eval_seam_36_hi]
  unfold sle
  decide

private theorem wad_seam_36 :
    sle (model_ln_wad_to_wad_evm (2 ^ (36 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (36 + 1))) = true := by
  rw [wad_eval_seam_36_lo, wad_eval_seam_36_hi]
  unfold sle
  decide

private theorem ray_eval_seam_37_lo :
    model_ln_wad_evm (2 ^ (37 + 1) - 1) = 115792089237316195423570985008687907853269984665625457100644965469379853516036 := by
  have hlog : Nat.log2 (2 ^ (37 + 1) - 1) = 37 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (37 + 1) - 1) % 2 ^ 256 = 2 ^ (37 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_37_hi :
    model_ln_wad_evm (2 ^ (37 + 1)) = 115792089237316195423570985008687907853269984665625457100644969107358660614367 := by
  have hlog : Nat.log2 (2 ^ (37 + 1)) = 38 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (37 + 1)) % 2 ^ 256 = 2 ^ (37 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_37_lo :
    model_ln_wad_to_wad_evm (2 ^ (37 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039442477069100511101402 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (37 + 1) - 1) % 2 ^ 256 = 2 ^ (37 + 1) - 1 by decide]
  rw [ray_eval_seam_37_lo]
  decide

private theorem wad_eval_seam_37_hi :
    model_ln_wad_to_wad_evm (2 ^ (37 + 1)) = 115792089237316195423570985008687907853269984665640564039442477069100514739381 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (37 + 1)) % 2 ^ 256 = 2 ^ (37 + 1) by decide]
  rw [ray_eval_seam_37_hi]
  decide

private theorem ray_seam_37 :
    sle (model_ln_wad_evm (2 ^ (37 + 1) - 1)) (model_ln_wad_evm (2 ^ (37 + 1))) = true := by
  rw [ray_eval_seam_37_lo, ray_eval_seam_37_hi]
  unfold sle
  decide

private theorem wad_seam_37 :
    sle (model_ln_wad_to_wad_evm (2 ^ (37 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (37 + 1))) = true := by
  rw [wad_eval_seam_37_lo, wad_eval_seam_37_hi]
  unfold sle
  decide

private theorem ray_eval_seam_38_lo :
    model_ln_wad_evm (2 ^ (38 + 1) - 1) = 115792089237316195423570985008687907853269984665626150247825527233678674298977 := by
  have hlog : Nat.log2 (2 ^ (38 + 1) - 1) = 38 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (38 + 1) - 1) % 2 ^ 256 = 2 ^ (38 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_38_hi :
    model_ln_wad_evm (2 ^ (38 + 1)) = 115792089237316195423570985008687907853269984665626150247825529052668077846488 := by
  have hlog : Nat.log2 (2 ^ (38 + 1)) = 39 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (38 + 1)) % 2 ^ 256 = 2 ^ (38 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_38_lo :
    model_ln_wad_to_wad_evm (2 ^ (38 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039443170216281072865701 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (38 + 1) - 1) % 2 ^ 256 = 2 ^ (38 + 1) - 1 by decide]
  rw [ray_eval_seam_38_lo]
  decide

private theorem wad_eval_seam_38_hi :
    model_ln_wad_to_wad_evm (2 ^ (38 + 1)) = 115792089237316195423570985008687907853269984665640564039443170216281074684690 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (38 + 1)) % 2 ^ 256 = 2 ^ (38 + 1) by decide]
  rw [ray_eval_seam_38_hi]
  decide

private theorem ray_seam_38 :
    sle (model_ln_wad_evm (2 ^ (38 + 1) - 1)) (model_ln_wad_evm (2 ^ (38 + 1))) = true := by
  rw [ray_eval_seam_38_lo, ray_eval_seam_38_hi]
  unfold sle
  decide

private theorem wad_seam_38 :
    sle (model_ln_wad_to_wad_evm (2 ^ (38 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (38 + 1))) = true := by
  rw [wad_eval_seam_38_lo, wad_eval_seam_38_hi]
  unfold sle
  decide

private theorem ray_eval_seam_39_lo :
    model_ln_wad_evm (2 ^ (39 + 1) - 1) = 115792089237316195423570985008687907853269984665626843395006088088482793305267 := by
  have hlog : Nat.log2 (2 ^ (39 + 1) - 1) = 39 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (39 + 1) - 1) % 2 ^ 256 = 2 ^ (39 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_39_hi :
    model_ln_wad_evm (2 ^ (39 + 1)) = 115792089237316195423570985008687907853269984665626843395006088997977495078609 := by
  have hlog : Nat.log2 (2 ^ (39 + 1)) = 40 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (39 + 1)) % 2 ^ 256 = 2 ^ (39 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_39_lo :
    model_ln_wad_to_wad_evm (2 ^ (39 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039443863363461633720505 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (39 + 1) - 1) % 2 ^ 256 = 2 ^ (39 + 1) - 1 by decide]
  rw [ray_eval_seam_39_lo]
  decide

private theorem wad_eval_seam_39_hi :
    model_ln_wad_to_wad_evm (2 ^ (39 + 1)) = 115792089237316195423570985008687907853269984665640564039443863363461634630000 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (39 + 1)) % 2 ^ 256 = 2 ^ (39 + 1) by decide]
  rw [ray_eval_seam_39_hi]
  decide

private theorem ray_seam_39 :
    sle (model_ln_wad_evm (2 ^ (39 + 1) - 1)) (model_ln_wad_evm (2 ^ (39 + 1))) = true := by
  rw [ray_eval_seam_39_lo, ray_eval_seam_39_hi]
  unfold sle
  decide

private theorem wad_seam_39 :
    sle (model_ln_wad_to_wad_evm (2 ^ (39 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (39 + 1))) = true := by
  rw [wad_eval_seam_39_lo, wad_eval_seam_39_hi]
  unfold sle
  decide

private theorem ray_eval_seam_40_lo :
    model_ln_wad_evm (2 ^ (40 + 1) - 1) = 115792089237316195423570985008687907853269984665627536542186648488539561424163 := by
  have hlog : Nat.log2 (2 ^ (40 + 1) - 1) = 40 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (40 + 1) - 1) % 2 ^ 256 = 2 ^ (40 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_40_hi :
    model_ln_wad_evm (2 ^ (40 + 1)) = 115792089237316195423570985008687907853269984665627536542186648943286912310731 := by
  have hlog : Nat.log2 (2 ^ (40 + 1)) = 41 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (40 + 1)) % 2 ^ 256 = 2 ^ (40 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_40_lo :
    model_ln_wad_to_wad_evm (2 ^ (40 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039444556510642194120562 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (40 + 1) - 1) % 2 ^ 256 = 2 ^ (40 + 1) - 1 by decide]
  rw [ray_eval_seam_40_lo]
  decide

private theorem wad_eval_seam_40_hi :
    model_ln_wad_to_wad_evm (2 ^ (40 + 1)) = 115792089237316195423570985008687907853269984665640564039444556510642194575309 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (40 + 1)) % 2 ^ 256 = 2 ^ (40 + 1) by decide]
  rw [ray_eval_seam_40_hi]
  decide

private theorem ray_seam_40 :
    sle (model_ln_wad_evm (2 ^ (40 + 1) - 1)) (model_ln_wad_evm (2 ^ (40 + 1))) = true := by
  rw [ray_eval_seam_40_lo, ray_eval_seam_40_hi]
  unfold sle
  decide

private theorem wad_seam_40 :
    sle (model_ln_wad_to_wad_evm (2 ^ (40 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (40 + 1))) = true := by
  rw [wad_eval_seam_40_lo, wad_eval_seam_40_hi]
  unfold sle
  decide

private theorem ray_eval_seam_41_lo :
    model_ln_wad_evm (2 ^ (41 + 1) - 1) = 115792089237316195423570985008687907853269984665628229689367208661222654099594 := by
  have hlog : Nat.log2 (2 ^ (41 + 1) - 1) = 41 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (41 + 1) - 1) % 2 ^ 256 = 2 ^ (41 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_41_hi :
    model_ln_wad_evm (2 ^ (41 + 1)) = 115792089237316195423570985008687907853269984665628229689367208888596329542852 := by
  have hlog : Nat.log2 (2 ^ (41 + 1)) = 42 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (41 + 1)) % 2 ^ 256 = 2 ^ (41 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_41_lo :
    model_ln_wad_to_wad_evm (2 ^ (41 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039445249657822754293245 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (41 + 1) - 1) % 2 ^ 256 = 2 ^ (41 + 1) - 1 by decide]
  rw [ray_eval_seam_41_lo]
  decide

private theorem wad_eval_seam_41_hi :
    model_ln_wad_to_wad_evm (2 ^ (41 + 1)) = 115792089237316195423570985008687907853269984665640564039445249657822754520619 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (41 + 1)) % 2 ^ 256 = 2 ^ (41 + 1) by decide]
  rw [ray_eval_seam_41_hi]
  decide

private theorem ray_seam_41 :
    sle (model_ln_wad_evm (2 ^ (41 + 1) - 1)) (model_ln_wad_evm (2 ^ (41 + 1))) = true := by
  rw [ray_eval_seam_41_lo, ray_eval_seam_41_hi]
  unfold sle
  decide

private theorem wad_seam_41 :
    sle (model_ln_wad_to_wad_evm (2 ^ (41 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (41 + 1))) = true := by
  rw [wad_eval_seam_41_lo, wad_eval_seam_41_hi]
  unfold sle
  decide

private theorem ray_eval_seam_42_lo :
    model_ln_wad_evm (2 ^ (42 + 1) - 1) = 115792089237316195423570985008687907853269984665628922836547768720218909053351 := by
  have hlog : Nat.log2 (2 ^ (42 + 1) - 1) = 42 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (42 + 1) - 1) % 2 ^ 256 = 2 ^ (42 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_42_hi :
    model_ln_wad_evm (2 ^ (42 + 1)) = 115792089237316195423570985008687907853269984665628922836547768833905746774974 := by
  have hlog : Nat.log2 (2 ^ (42 + 1)) = 43 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (42 + 1)) % 2 ^ 256 = 2 ^ (42 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_42_lo :
    model_ln_wad_to_wad_evm (2 ^ (42 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039445942805003314352241 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (42 + 1) - 1) % 2 ^ 256 = 2 ^ (42 + 1) - 1 by decide]
  rw [ray_eval_seam_42_lo]
  decide

private theorem wad_eval_seam_42_hi :
    model_ln_wad_to_wad_evm (2 ^ (42 + 1)) = 115792089237316195423570985008687907853269984665640564039445942805003314465928 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (42 + 1)) % 2 ^ 256 = 2 ^ (42 + 1) by decide]
  rw [ray_eval_seam_42_hi]
  decide

private theorem ray_seam_42 :
    sle (model_ln_wad_evm (2 ^ (42 + 1) - 1)) (model_ln_wad_evm (2 ^ (42 + 1))) = true := by
  rw [ray_eval_seam_42_lo, ray_eval_seam_42_hi]
  unfold sle
  decide

private theorem wad_seam_42 :
    sle (model_ln_wad_to_wad_evm (2 ^ (42 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (42 + 1))) = true := by
  rw [wad_eval_seam_42_lo, wad_eval_seam_42_hi]
  unfold sle
  decide

private theorem ray_eval_seam_43_lo :
    model_ln_wad_evm (2 ^ (43 + 1) - 1) = 115792089237316195423570985008687907853269984665629615983728328722371745146285 := by
  have hlog : Nat.log2 (2 ^ (43 + 1) - 1) = 43 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (43 + 1) - 1) % 2 ^ 256 = 2 ^ (43 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_43_hi :
    model_ln_wad_evm (2 ^ (43 + 1)) = 115792089237316195423570985008687907853269984665629615983728328779215164007095 := by
  have hlog : Nat.log2 (2 ^ (43 + 1)) = 44 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (43 + 1)) % 2 ^ 256 = 2 ^ (43 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_43_lo :
    model_ln_wad_to_wad_evm (2 ^ (43 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039446635952183874354394 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (43 + 1) - 1) % 2 ^ 256 = 2 ^ (43 + 1) - 1 by decide]
  rw [ray_eval_seam_43_lo]
  decide

private theorem wad_eval_seam_43_hi :
    model_ln_wad_to_wad_evm (2 ^ (43 + 1)) = 115792089237316195423570985008687907853269984665640564039446635952183874411238 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (43 + 1)) % 2 ^ 256 = 2 ^ (43 + 1) by decide]
  rw [ray_eval_seam_43_hi]
  decide

private theorem ray_seam_43 :
    sle (model_ln_wad_evm (2 ^ (43 + 1) - 1)) (model_ln_wad_evm (2 ^ (43 + 1))) = true := by
  rw [ray_eval_seam_43_lo, ray_eval_seam_43_hi]
  unfold sle
  decide

private theorem wad_seam_43 :
    sle (model_ln_wad_to_wad_evm (2 ^ (43 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (43 + 1))) = true := by
  rw [wad_eval_seam_43_lo, wad_eval_seam_43_hi]
  unfold sle
  decide

private theorem ray_eval_seam_44_lo :
    model_ln_wad_evm (2 ^ (44 + 1) - 1) = 115792089237316195423570985008687907853269984665630309130908888696102871808812 := by
  have hlog : Nat.log2 (2 ^ (44 + 1) - 1) = 44 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (44 + 1) - 1) % 2 ^ 256 = 2 ^ (44 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_44_hi :
    model_ln_wad_evm (2 ^ (44 + 1)) = 115792089237316195423570985008687907853269984665630309130908888724524581239217 := by
  have hlog : Nat.log2 (2 ^ (44 + 1)) = 45 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (44 + 1)) % 2 ^ 256 = 2 ^ (44 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_44_lo :
    model_ln_wad_to_wad_evm (2 ^ (44 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039447329099364434328125 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (44 + 1) - 1) % 2 ^ 256 = 2 ^ (44 + 1) - 1 by decide]
  rw [ray_eval_seam_44_lo]
  decide

private theorem wad_eval_seam_44_hi :
    model_ln_wad_to_wad_evm (2 ^ (44 + 1)) = 115792089237316195423570985008687907853269984665640564039447329099364434356547 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (44 + 1)) % 2 ^ 256 = 2 ^ (44 + 1) by decide]
  rw [ray_eval_seam_44_hi]
  decide

private theorem ray_seam_44 :
    sle (model_ln_wad_evm (2 ^ (44 + 1) - 1)) (model_ln_wad_evm (2 ^ (44 + 1))) = true := by
  rw [ray_eval_seam_44_lo, ray_eval_seam_44_hi]
  unfold sle
  decide

private theorem wad_seam_44 :
    sle (model_ln_wad_to_wad_evm (2 ^ (44 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (44 + 1))) = true := by
  rw [wad_eval_seam_44_lo, wad_eval_seam_44_hi]
  unfold sle
  decide

private theorem ray_eval_seam_45_lo :
    model_ln_wad_evm (2 ^ (45 + 1) - 1) = 115792089237316195423570985008687907853269984665631002278089448655623143756135 := by
  have hlog : Nat.log2 (2 ^ (45 + 1) - 1) = 45 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (45 + 1) - 1) % 2 ^ 256 = 2 ^ (45 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_45_hi :
    model_ln_wad_evm (2 ^ (45 + 1)) = 115792089237316195423570985008687907853269984665631002278089448669833998471338 := by
  have hlog : Nat.log2 (2 ^ (45 + 1)) = 46 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (45 + 1)) % 2 ^ 256 = 2 ^ (45 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_45_lo :
    model_ln_wad_to_wad_evm (2 ^ (45 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039448022246544994287646 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (45 + 1) - 1) % 2 ^ 256 = 2 ^ (45 + 1) - 1 by decide]
  rw [ray_eval_seam_45_lo]
  decide

private theorem wad_eval_seam_45_hi :
    model_ln_wad_to_wad_evm (2 ^ (45 + 1)) = 115792089237316195423570985008687907853269984665640564039448022246544994301856 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (45 + 1)) % 2 ^ 256 = 2 ^ (45 + 1) by decide]
  rw [ray_eval_seam_45_hi]
  decide

private theorem ray_seam_45 :
    sle (model_ln_wad_evm (2 ^ (45 + 1) - 1)) (model_ln_wad_evm (2 ^ (45 + 1))) = true := by
  rw [ray_eval_seam_45_lo, ray_eval_seam_45_hi]
  unfold sle
  decide

private theorem wad_seam_45 :
    sle (model_ln_wad_to_wad_evm (2 ^ (45 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (45 + 1))) = true := by
  rw [wad_eval_seam_45_lo, wad_eval_seam_45_hi]
  unfold sle
  decide

private theorem ray_eval_seam_46_lo :
    model_ln_wad_evm (2 ^ (46 + 1) - 1) = 115792089237316195423570985008687907853269984665631695425270008608037988345858 := by
  have hlog : Nat.log2 (2 ^ (46 + 1) - 1) = 46 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (46 + 1) - 1) % 2 ^ 256 = 2 ^ (46 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_46_hi :
    model_ln_wad_evm (2 ^ (46 + 1)) = 115792089237316195423570985008687907853269984665631695425270008615143415703460 := by
  have hlog : Nat.log2 (2 ^ (46 + 1)) = 47 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (46 + 1)) % 2 ^ 256 = 2 ^ (46 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_46_lo :
    model_ln_wad_to_wad_evm (2 ^ (46 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039448715393725554240060 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (46 + 1) - 1) % 2 ^ 256 = 2 ^ (46 + 1) - 1 by decide]
  rw [ray_eval_seam_46_lo]
  decide

private theorem wad_eval_seam_46_hi :
    model_ln_wad_to_wad_evm (2 ^ (46 + 1)) = 115792089237316195423570985008687907853269984665640564039448715393725554247166 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (46 + 1)) % 2 ^ 256 = 2 ^ (46 + 1) by decide]
  rw [ray_eval_seam_46_hi]
  decide

private theorem ray_seam_46 :
    sle (model_ln_wad_evm (2 ^ (46 + 1) - 1)) (model_ln_wad_evm (2 ^ (46 + 1))) = true := by
  rw [ray_eval_seam_46_lo, ray_eval_seam_46_hi]
  unfold sle
  decide

private theorem wad_seam_46 :
    sle (model_ln_wad_to_wad_evm (2 ^ (46 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (46 + 1))) = true := by
  rw [wad_eval_seam_46_lo, wad_eval_seam_46_hi]
  unfold sle
  decide

private theorem ray_eval_seam_47_lo :
    model_ln_wad_evm (2 ^ (47 + 1) - 1) = 115792089237316195423570985008687907853269984665632388572450568556900119256780 := by
  have hlog : Nat.log2 (2 ^ (47 + 1) - 1) = 47 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (47 + 1) - 1) % 2 ^ 256 = 2 ^ (47 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_47_hi :
    model_ln_wad_evm (2 ^ (47 + 1)) = 115792089237316195423570985008687907853269984665632388572450568560452832935581 := by
  have hlog : Nat.log2 (2 ^ (47 + 1)) = 48 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (47 + 1)) % 2 ^ 256 = 2 ^ (47 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_47_lo :
    model_ln_wad_to_wad_evm (2 ^ (47 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039449408540906114188922 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (47 + 1) - 1) % 2 ^ 256 = 2 ^ (47 + 1) - 1 by decide]
  rw [ray_eval_seam_47_lo]
  decide

private theorem wad_eval_seam_47_hi :
    model_ln_wad_to_wad_evm (2 ^ (47 + 1)) = 115792089237316195423570985008687907853269984665640564039449408540906114192475 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (47 + 1)) % 2 ^ 256 = 2 ^ (47 + 1) by decide]
  rw [ray_eval_seam_47_hi]
  decide

private theorem ray_seam_47 :
    sle (model_ln_wad_evm (2 ^ (47 + 1) - 1)) (model_ln_wad_evm (2 ^ (47 + 1))) = true := by
  rw [ray_eval_seam_47_lo, ray_eval_seam_47_hi]
  unfold sle
  decide

private theorem wad_seam_47 :
    sle (model_ln_wad_to_wad_evm (2 ^ (47 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (47 + 1))) = true := by
  rw [wad_eval_seam_47_lo, wad_eval_seam_47_hi]
  unfold sle
  decide

private theorem ray_eval_seam_48_lo :
    model_ln_wad_evm (2 ^ (48 + 1) - 1) = 115792089237316195423570985008687907853269984665633081719631128503985893328302 := by
  have hlog : Nat.log2 (2 ^ (48 + 1) - 1) = 48 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (48 + 1) - 1) % 2 ^ 256 = 2 ^ (48 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_48_hi :
    model_ln_wad_evm (2 ^ (48 + 1)) = 115792089237316195423570985008687907853269984665633081719631128505762250167703 := by
  have hlog : Nat.log2 (2 ^ (48 + 1)) = 49 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (48 + 1)) % 2 ^ 256 = 2 ^ (48 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_48_lo :
    model_ln_wad_to_wad_evm (2 ^ (48 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039450101688086674136008 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (48 + 1) - 1) % 2 ^ 256 = 2 ^ (48 + 1) - 1 by decide]
  rw [ray_eval_seam_48_lo]
  decide

private theorem wad_eval_seam_48_hi :
    model_ln_wad_to_wad_evm (2 ^ (48 + 1)) = 115792089237316195423570985008687907853269984665640564039450101688086674137785 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (48 + 1)) % 2 ^ 256 = 2 ^ (48 + 1) by decide]
  rw [ray_eval_seam_48_hi]
  decide

private theorem ray_seam_48 :
    sle (model_ln_wad_evm (2 ^ (48 + 1) - 1)) (model_ln_wad_evm (2 ^ (48 + 1))) = true := by
  rw [ray_eval_seam_48_lo, ray_eval_seam_48_hi]
  unfold sle
  decide

private theorem wad_seam_48 :
    sle (model_ln_wad_to_wad_evm (2 ^ (48 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (48 + 1))) = true := by
  rw [wad_eval_seam_48_lo, wad_eval_seam_48_hi]
  unfold sle
  decide

private theorem ray_eval_seam_49_lo :
    model_ln_wad_evm (2 ^ (49 + 1) - 1) = 115792089237316195423570985008687907853269984665633774866811688450183488980123 := by
  have hlog : Nat.log2 (2 ^ (49 + 1) - 1) = 49 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (49 + 1) - 1) % 2 ^ 256 = 2 ^ (49 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_49_hi :
    model_ln_wad_evm (2 ^ (49 + 1)) = 115792089237316195423570985008687907853269984665633774866811688451071667399824 := by
  have hlog : Nat.log2 (2 ^ (49 + 1)) = 50 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (49 + 1)) % 2 ^ 256 = 2 ^ (49 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_49_lo :
    model_ln_wad_to_wad_evm (2 ^ (49 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039450794835267234082206 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (49 + 1) - 1) % 2 ^ 256 = 2 ^ (49 + 1) - 1 by decide]
  rw [ray_eval_seam_49_lo]
  decide

private theorem wad_eval_seam_49_hi :
    model_ln_wad_to_wad_evm (2 ^ (49 + 1)) = 115792089237316195423570985008687907853269984665640564039450794835267234083094 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (49 + 1)) % 2 ^ 256 = 2 ^ (49 + 1) by decide]
  rw [ray_eval_seam_49_hi]
  decide

private theorem ray_seam_49 :
    sle (model_ln_wad_evm (2 ^ (49 + 1) - 1)) (model_ln_wad_evm (2 ^ (49 + 1))) = true := by
  rw [ray_eval_seam_49_lo, ray_eval_seam_49_hi]
  unfold sle
  decide

private theorem wad_seam_49 :
    sle (model_ln_wad_to_wad_evm (2 ^ (49 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (49 + 1))) = true := by
  rw [wad_eval_seam_49_lo, wad_eval_seam_49_hi]
  unfold sle
  decide

private theorem ray_eval_seam_50_lo :
    model_ln_wad_evm (2 ^ (50 + 1) - 1) = 115792089237316195423570985008687907853269984665634468013992248395936995422095 := by
  have hlog : Nat.log2 (2 ^ (50 + 1) - 1) = 50 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (50 + 1) - 1) % 2 ^ 256 = 2 ^ (50 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_50_hi :
    model_ln_wad_evm (2 ^ (50 + 1)) = 115792089237316195423570985008687907853269984665634468013992248396381084631946 := by
  have hlog : Nat.log2 (2 ^ (50 + 1)) = 51 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (50 + 1)) % 2 ^ 256 = 2 ^ (50 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_50_lo :
    model_ln_wad_to_wad_evm (2 ^ (50 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039451487982447794027959 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (50 + 1) - 1) % 2 ^ 256 = 2 ^ (50 + 1) - 1 by decide]
  rw [ray_eval_seam_50_lo]
  decide

private theorem wad_eval_seam_50_hi :
    model_ln_wad_to_wad_evm (2 ^ (50 + 1)) = 115792089237316195423570985008687907853269984665640564039451487982447794028403 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (50 + 1)) % 2 ^ 256 = 2 ^ (50 + 1) by decide]
  rw [ray_eval_seam_50_hi]
  decide

private theorem ray_seam_50 :
    sle (model_ln_wad_evm (2 ^ (50 + 1) - 1)) (model_ln_wad_evm (2 ^ (50 + 1))) = true := by
  rw [ray_eval_seam_50_lo, ray_eval_seam_50_hi]
  unfold sle
  decide

private theorem wad_seam_50 :
    sle (model_ln_wad_to_wad_evm (2 ^ (50 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (50 + 1))) = true := by
  rw [wad_eval_seam_50_lo, wad_eval_seam_50_hi]
  unfold sle
  decide

private theorem ray_eval_seam_51_lo :
    model_ln_wad_evm (2 ^ (51 + 1) - 1) = 115792089237316195423570985008687907853269984665635161161172808341468457259141 := by
  have hlog : Nat.log2 (2 ^ (51 + 1) - 1) = 51 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (51 + 1) - 1) % 2 ^ 256 = 2 ^ (51 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_51_hi :
    model_ln_wad_evm (2 ^ (51 + 1)) = 115792089237316195423570985008687907853269984665635161161172808341690501864067 := by
  have hlog : Nat.log2 (2 ^ (51 + 1)) = 52 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (51 + 1)) % 2 ^ 256 = 2 ^ (51 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_51_lo :
    model_ln_wad_to_wad_evm (2 ^ (51 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039452181129628353973491 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (51 + 1) - 1) % 2 ^ 256 = 2 ^ (51 + 1) - 1 by decide]
  rw [ray_eval_seam_51_lo]
  decide

private theorem wad_eval_seam_51_hi :
    model_ln_wad_to_wad_evm (2 ^ (51 + 1)) = 115792089237316195423570985008687907853269984665640564039452181129628353973713 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (51 + 1)) % 2 ^ 256 = 2 ^ (51 + 1) by decide]
  rw [ray_eval_seam_51_hi]
  decide

private theorem ray_seam_51 :
    sle (model_ln_wad_evm (2 ^ (51 + 1) - 1)) (model_ln_wad_evm (2 ^ (51 + 1))) = true := by
  rw [ray_eval_seam_51_lo, ray_eval_seam_51_hi]
  unfold sle
  decide

private theorem wad_seam_51 :
    sle (model_ln_wad_to_wad_evm (2 ^ (51 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (51 + 1))) = true := by
  rw [wad_eval_seam_51_lo, wad_eval_seam_51_hi]
  unfold sle
  decide

private theorem ray_eval_seam_52_lo :
    model_ln_wad_evm (2 ^ (52 + 1) - 1) = 115792089237316195423570985008687907853269984665635854308353368286888896793725 := by
  have hlog : Nat.log2 (2 ^ (52 + 1) - 1) = 52 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (52 + 1) - 1) % 2 ^ 256 = 2 ^ (52 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_52_hi :
    model_ln_wad_evm (2 ^ (52 + 1)) = 115792089237316195423570985008687907853269984665635854308353368286999919096188 := by
  have hlog : Nat.log2 (2 ^ (52 + 1)) = 53 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (52 + 1)) % 2 ^ 256 = 2 ^ (52 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_52_lo :
    model_ln_wad_to_wad_evm (2 ^ (52 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039452874276808913918911 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (52 + 1) - 1) % 2 ^ 256 = 2 ^ (52 + 1) - 1 by decide]
  rw [ray_eval_seam_52_lo]
  decide

private theorem wad_eval_seam_52_hi :
    model_ln_wad_to_wad_evm (2 ^ (52 + 1)) = 115792089237316195423570985008687907853269984665640564039452874276808913919022 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (52 + 1)) % 2 ^ 256 = 2 ^ (52 + 1) by decide]
  rw [ray_eval_seam_52_hi]
  decide

private theorem ray_seam_52 :
    sle (model_ln_wad_evm (2 ^ (52 + 1) - 1)) (model_ln_wad_evm (2 ^ (52 + 1))) = true := by
  rw [ray_eval_seam_52_lo, ray_eval_seam_52_hi]
  unfold sle
  decide

private theorem wad_seam_52 :
    sle (model_ln_wad_to_wad_evm (2 ^ (52 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (52 + 1))) = true := by
  rw [wad_eval_seam_52_lo, wad_eval_seam_52_hi]
  unfold sle
  decide

private theorem ray_eval_seam_53_lo :
    model_ln_wad_evm (2 ^ (53 + 1) - 1) = 115792089237316195423570985008687907853269984665636547455533928232253825177078 := by
  have hlog : Nat.log2 (2 ^ (53 + 1) - 1) = 53 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (53 + 1) - 1) % 2 ^ 256 = 2 ^ (53 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_53_hi :
    model_ln_wad_evm (2 ^ (53 + 1)) = 115792089237316195423570985008687907853269984665636547455533928232309336328310 := by
  have hlog : Nat.log2 (2 ^ (53 + 1)) = 54 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (53 + 1)) % 2 ^ 256 = 2 ^ (53 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_53_lo :
    model_ln_wad_to_wad_evm (2 ^ (53 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039453567423989473864276 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (53 + 1) - 1) % 2 ^ 256 = 2 ^ (53 + 1) - 1 by decide]
  rw [ray_eval_seam_53_lo]
  decide

private theorem wad_eval_seam_53_hi :
    model_ln_wad_to_wad_evm (2 ^ (53 + 1)) = 115792089237316195423570985008687907853269984665640564039453567423989473864332 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (53 + 1)) % 2 ^ 256 = 2 ^ (53 + 1) by decide]
  rw [ray_eval_seam_53_hi]
  decide

private theorem ray_seam_53 :
    sle (model_ln_wad_evm (2 ^ (53 + 1) - 1)) (model_ln_wad_evm (2 ^ (53 + 1))) = true := by
  rw [ray_eval_seam_53_lo, ray_eval_seam_53_hi]
  unfold sle
  decide

private theorem wad_seam_53 :
    sle (model_ln_wad_to_wad_evm (2 ^ (53 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (53 + 1))) = true := by
  rw [wad_eval_seam_53_lo, wad_eval_seam_53_hi]
  unfold sle
  decide

private theorem ray_eval_seam_54_lo :
    model_ln_wad_evm (2 ^ (54 + 1) - 1) = 115792089237316195423570985008687907853269984665637240602714488177590997984815 := by
  have hlog : Nat.log2 (2 ^ (54 + 1) - 1) = 54 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (54 + 1) - 1) % 2 ^ 256 = 2 ^ (54 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_54_hi :
    model_ln_wad_evm (2 ^ (54 + 1)) = 115792089237316195423570985008687907853269984665637240602714488177618753560431 := by
  have hlog : Nat.log2 (2 ^ (54 + 1)) = 55 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (54 + 1)) % 2 ^ 256 = 2 ^ (54 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_54_lo :
    model_ln_wad_to_wad_evm (2 ^ (54 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039454260571170033809613 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (54 + 1) - 1) % 2 ^ 256 = 2 ^ (54 + 1) - 1 by decide]
  rw [ray_eval_seam_54_lo]
  decide

private theorem wad_eval_seam_54_hi :
    model_ln_wad_to_wad_evm (2 ^ (54 + 1)) = 115792089237316195423570985008687907853269984665640564039454260571170033809641 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (54 + 1)) % 2 ^ 256 = 2 ^ (54 + 1) by decide]
  rw [ray_eval_seam_54_hi]
  decide

private theorem ray_seam_54 :
    sle (model_ln_wad_evm (2 ^ (54 + 1) - 1)) (model_ln_wad_evm (2 ^ (54 + 1))) = true := by
  rw [ray_eval_seam_54_lo, ray_eval_seam_54_hi]
  unfold sle
  decide

private theorem wad_seam_54 :
    sle (model_ln_wad_to_wad_evm (2 ^ (54 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (54 + 1))) = true := by
  rw [wad_eval_seam_54_lo, wad_eval_seam_54_hi]
  unfold sle
  decide

private theorem ray_eval_seam_55_lo :
    model_ln_wad_evm (2 ^ (55 + 1) - 1) = 115792089237316195423570985008687907853269984665637933749895048122914293004744 := by
  have hlog : Nat.log2 (2 ^ (55 + 1) - 1) = 55 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (55 + 1) - 1) % 2 ^ 256 = 2 ^ (55 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_55_hi :
    model_ln_wad_evm (2 ^ (55 + 1)) = 115792089237316195423570985008687907853269984665637933749895048122928170792553 := by
  have hlog : Nat.log2 (2 ^ (55 + 1)) = 56 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (55 + 1)) % 2 ^ 256 = 2 ^ (55 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_55_lo :
    model_ln_wad_to_wad_evm (2 ^ (55 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039454953718350593754937 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (55 + 1) - 1) % 2 ^ 256 = 2 ^ (55 + 1) - 1 by decide]
  rw [ray_eval_seam_55_lo]
  decide

private theorem wad_eval_seam_55_hi :
    model_ln_wad_to_wad_evm (2 ^ (55 + 1)) = 115792089237316195423570985008687907853269984665640564039454953718350593754951 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (55 + 1)) % 2 ^ 256 = 2 ^ (55 + 1) by decide]
  rw [ray_eval_seam_55_hi]
  decide

private theorem ray_seam_55 :
    sle (model_ln_wad_evm (2 ^ (55 + 1) - 1)) (model_ln_wad_evm (2 ^ (55 + 1))) = true := by
  rw [ray_eval_seam_55_lo, ray_eval_seam_55_hi]
  unfold sle
  decide

private theorem wad_seam_55 :
    sle (model_ln_wad_to_wad_evm (2 ^ (55 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (55 + 1))) = true := by
  rw [wad_eval_seam_55_lo, wad_eval_seam_55_hi]
  unfold sle
  decide

private theorem ray_eval_seam_56_lo :
    model_ln_wad_evm (2 ^ (56 + 1) - 1) = 115792089237316195423570985008687907853269984665638626897075608068230649130770 := by
  have hlog : Nat.log2 (2 ^ (56 + 1) - 1) = 56 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (56 + 1) - 1) % 2 ^ 256 = 2 ^ (56 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_56_hi :
    model_ln_wad_evm (2 ^ (56 + 1)) = 115792089237316195423570985008687907853269984665638626897075608068237588024674 := by
  have hlog : Nat.log2 (2 ^ (56 + 1)) = 57 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (56 + 1)) % 2 ^ 256 = 2 ^ (56 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_56_lo :
    model_ln_wad_to_wad_evm (2 ^ (56 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039455646865531153700253 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (56 + 1) - 1) % 2 ^ 256 = 2 ^ (56 + 1) - 1 by decide]
  rw [ray_eval_seam_56_lo]
  decide

private theorem wad_eval_seam_56_hi :
    model_ln_wad_to_wad_evm (2 ^ (56 + 1)) = 115792089237316195423570985008687907853269984665640564039455646865531153700260 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (56 + 1)) % 2 ^ 256 = 2 ^ (56 + 1) by decide]
  rw [ray_eval_seam_56_hi]
  decide

private theorem ray_seam_56 :
    sle (model_ln_wad_evm (2 ^ (56 + 1) - 1)) (model_ln_wad_evm (2 ^ (56 + 1))) = true := by
  rw [ray_eval_seam_56_lo, ray_eval_seam_56_hi]
  unfold sle
  decide

private theorem wad_seam_56 :
    sle (model_ln_wad_to_wad_evm (2 ^ (56 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (56 + 1))) = true := by
  rw [wad_eval_seam_56_lo, wad_eval_seam_56_hi]
  unfold sle
  decide

private theorem ray_eval_seam_57_lo :
    model_ln_wad_evm (2 ^ (57 + 1) - 1) = 115792089237316195423570985008687907853269984665639320044256168013543535809843 := by
  have hlog : Nat.log2 (2 ^ (57 + 1) - 1) = 57 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (57 + 1) - 1) % 2 ^ 256 = 2 ^ (57 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_57_hi :
    model_ln_wad_evm (2 ^ (57 + 1)) = 115792089237316195423570985008687907853269984665639320044256168013547005256796 := by
  have hlog : Nat.log2 (2 ^ (57 + 1)) = 58 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (57 + 1)) % 2 ^ 256 = 2 ^ (57 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_57_lo :
    model_ln_wad_to_wad_evm (2 ^ (57 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039456340012711713645566 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (57 + 1) - 1) % 2 ^ 256 = 2 ^ (57 + 1) - 1 by decide]
  rw [ray_eval_seam_57_lo]
  decide

private theorem wad_eval_seam_57_hi :
    model_ln_wad_to_wad_evm (2 ^ (57 + 1)) = 115792089237316195423570985008687907853269984665640564039456340012711713645569 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (57 + 1)) % 2 ^ 256 = 2 ^ (57 + 1) by decide]
  rw [ray_eval_seam_57_hi]
  decide

private theorem ray_seam_57 :
    sle (model_ln_wad_evm (2 ^ (57 + 1) - 1)) (model_ln_wad_evm (2 ^ (57 + 1))) = true := by
  rw [ray_eval_seam_57_lo, ray_eval_seam_57_hi]
  unfold sle
  decide

private theorem wad_seam_57 :
    sle (model_ln_wad_to_wad_evm (2 ^ (57 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (57 + 1))) = true := by
  rw [wad_eval_seam_57_lo, wad_eval_seam_57_hi]
  unfold sle
  decide

private theorem ray_eval_seam_58_lo :
    model_ln_wad_evm (2 ^ (58 + 1) - 1) = 115792089237316195423570985008687907853269984665640013191436727958854687765441 := by
  have hlog : Nat.log2 (2 ^ (58 + 1) - 1) = 58 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (58 + 1) - 1) % 2 ^ 256 = 2 ^ (58 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_58_hi :
    model_ln_wad_evm (2 ^ (58 + 1)) = 115792089237316195423570985008687907853269984665640013191436727958856422488917 := by
  have hlog : Nat.log2 (2 ^ (58 + 1)) = 59 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (58 + 1)) % 2 ^ 256 = 2 ^ (58 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_58_lo :
    model_ln_wad_to_wad_evm (2 ^ (58 + 1) - 1) = 115792089237316195423570985008687907853269984665640564039457033159892273590877 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (58 + 1) - 1) % 2 ^ 256 = 2 ^ (58 + 1) - 1 by decide]
  rw [ray_eval_seam_58_lo]
  decide

private theorem wad_eval_seam_58_hi :
    model_ln_wad_to_wad_evm (2 ^ (58 + 1)) = 115792089237316195423570985008687907853269984665640564039457033159892273590879 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (58 + 1)) % 2 ^ 256 = 2 ^ (58 + 1) by decide]
  rw [ray_eval_seam_58_hi]
  decide

private theorem ray_seam_58 :
    sle (model_ln_wad_evm (2 ^ (58 + 1) - 1)) (model_ln_wad_evm (2 ^ (58 + 1))) = true := by
  rw [ray_eval_seam_58_lo, ray_eval_seam_58_hi]
  unfold sle
  decide

private theorem wad_seam_58 :
    sle (model_ln_wad_to_wad_evm (2 ^ (58 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (58 + 1))) = true := by
  rw [wad_eval_seam_58_lo, wad_eval_seam_58_hi]
  unfold sle
  decide

private theorem ray_eval_seam_59_lo :
    model_ln_wad_evm (2 ^ (59 + 1) - 1) = 142299159703896251842719364 := by
  have hlog : Nat.log2 (2 ^ (59 + 1) - 1) = 59 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (59 + 1) - 1) % 2 ^ 256 = 2 ^ (59 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_59_hi :
    model_ln_wad_evm (2 ^ (59 + 1)) = 142299159703896252710081103 := by
  have hlog : Nat.log2 (2 ^ (59 + 1)) = 60 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (59 + 1)) % 2 ^ 256 = 2 ^ (59 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_59_lo :
    model_ln_wad_to_wad_evm (2 ^ (59 + 1) - 1) = 142299159703896251 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (59 + 1) - 1) % 2 ^ 256 = 2 ^ (59 + 1) - 1 by decide]
  rw [ray_eval_seam_59_lo]
  decide

private theorem wad_eval_seam_59_hi :
    model_ln_wad_to_wad_evm (2 ^ (59 + 1)) = 142299159703896252 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (59 + 1)) % 2 ^ 256 = 2 ^ (59 + 1) by decide]
  rw [ray_eval_seam_59_hi]
  decide

private theorem ray_seam_59 :
    sle (model_ln_wad_evm (2 ^ (59 + 1) - 1)) (model_ln_wad_evm (2 ^ (59 + 1))) = true := by
  rw [ray_eval_seam_59_lo, ray_eval_seam_59_hi]
  unfold sle
  decide

private theorem wad_seam_59 :
    sle (model_ln_wad_to_wad_evm (2 ^ (59 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (59 + 1))) = true := by
  rw [wad_eval_seam_59_lo, wad_eval_seam_59_hi]
  unfold sle
  decide

private theorem ray_eval_seam_60_lo :
    model_ln_wad_evm (2 ^ (60 + 1) - 1) = 835446340263841561693632354 := by
  have hlog : Nat.log2 (2 ^ (60 + 1) - 1) = 60 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (60 + 1) - 1) % 2 ^ 256 = 2 ^ (60 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_60_hi :
    model_ln_wad_evm (2 ^ (60 + 1)) = 835446340263841562127313224 := by
  have hlog : Nat.log2 (2 ^ (60 + 1)) = 61 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (60 + 1)) % 2 ^ 256 = 2 ^ (60 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_60_lo :
    model_ln_wad_to_wad_evm (2 ^ (60 + 1) - 1) = 835446340263841561 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (60 + 1) - 1) % 2 ^ 256 = 2 ^ (60 + 1) - 1 by decide]
  rw [ray_eval_seam_60_lo]
  decide

private theorem wad_eval_seam_60_hi :
    model_ln_wad_to_wad_evm (2 ^ (60 + 1)) = 835446340263841562 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (60 + 1)) % 2 ^ 256 = 2 ^ (60 + 1) by decide]
  rw [ray_eval_seam_60_hi]
  decide

private theorem ray_seam_60 :
    sle (model_ln_wad_evm (2 ^ (60 + 1) - 1)) (model_ln_wad_evm (2 ^ (60 + 1))) = true := by
  rw [ray_eval_seam_60_lo, ray_eval_seam_60_hi]
  unfold sle
  decide

private theorem wad_seam_60 :
    sle (model_ln_wad_to_wad_evm (2 ^ (60 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (60 + 1))) = true := by
  rw [wad_eval_seam_60_lo, wad_eval_seam_60_hi]
  unfold sle
  decide

private theorem ray_eval_seam_61_lo :
    model_ln_wad_evm (2 ^ (61 + 1) - 1) = 1528593520823786871327704910 := by
  have hlog : Nat.log2 (2 ^ (61 + 1) - 1) = 61 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (61 + 1) - 1) % 2 ^ 256 = 2 ^ (61 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_61_hi :
    model_ln_wad_evm (2 ^ (61 + 1)) = 1528593520823786871544545346 := by
  have hlog : Nat.log2 (2 ^ (61 + 1)) = 62 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (61 + 1)) % 2 ^ 256 = 2 ^ (61 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_61_lo :
    model_ln_wad_to_wad_evm (2 ^ (61 + 1) - 1) = 1528593520823786871 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (61 + 1) - 1) % 2 ^ 256 = 2 ^ (61 + 1) - 1 by decide]
  rw [ray_eval_seam_61_lo]
  decide

private theorem wad_eval_seam_61_hi :
    model_ln_wad_to_wad_evm (2 ^ (61 + 1)) = 1528593520823786871 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (61 + 1)) % 2 ^ 256 = 2 ^ (61 + 1) by decide]
  rw [ray_eval_seam_61_hi]
  decide

private theorem ray_seam_61 :
    sle (model_ln_wad_evm (2 ^ (61 + 1) - 1)) (model_ln_wad_evm (2 ^ (61 + 1))) = true := by
  rw [ray_eval_seam_61_lo, ray_eval_seam_61_hi]
  unfold sle
  decide

private theorem wad_seam_61 :
    sle (model_ln_wad_to_wad_evm (2 ^ (61 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (61 + 1))) = true := by
  rw [wad_eval_seam_61_lo, wad_eval_seam_61_hi]
  unfold sle
  decide

private theorem ray_eval_seam_62_lo :
    model_ln_wad_evm (2 ^ (62 + 1) - 1) = 2221740701383732180853357249 := by
  have hlog : Nat.log2 (2 ^ (62 + 1) - 1) = 62 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (62 + 1) - 1) % 2 ^ 256 = 2 ^ (62 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_62_hi :
    model_ln_wad_evm (2 ^ (62 + 1)) = 2221740701383732180961777467 := by
  have hlog : Nat.log2 (2 ^ (62 + 1)) = 63 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (62 + 1)) % 2 ^ 256 = 2 ^ (62 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_62_lo :
    model_ln_wad_to_wad_evm (2 ^ (62 + 1) - 1) = 2221740701383732180 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (62 + 1) - 1) % 2 ^ 256 = 2 ^ (62 + 1) - 1 by decide]
  rw [ray_eval_seam_62_lo]
  decide

private theorem wad_eval_seam_62_hi :
    model_ln_wad_to_wad_evm (2 ^ (62 + 1)) = 2221740701383732180 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (62 + 1)) % 2 ^ 256 = 2 ^ (62 + 1) by decide]
  rw [ray_eval_seam_62_hi]
  decide

private theorem ray_seam_62 :
    sle (model_ln_wad_evm (2 ^ (62 + 1) - 1)) (model_ln_wad_evm (2 ^ (62 + 1))) = true := by
  rw [ray_eval_seam_62_lo, ray_eval_seam_62_hi]
  unfold sle
  decide

private theorem wad_seam_62 :
    sle (model_ln_wad_to_wad_evm (2 ^ (62 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (62 + 1))) = true := by
  rw [wad_eval_seam_62_lo, wad_eval_seam_62_hi]
  unfold sle
  decide

private theorem ray_eval_seam_63_lo :
    model_ln_wad_evm (2 ^ (63 + 1) - 1) = 2914887881943677490324799479 := by
  have hlog : Nat.log2 (2 ^ (63 + 1) - 1) = 63 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (63 + 1) - 1) % 2 ^ 256 = 2 ^ (63 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_63_hi :
    model_ln_wad_evm (2 ^ (63 + 1)) = 2914887881943677490379009588 := by
  have hlog : Nat.log2 (2 ^ (63 + 1)) = 64 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (63 + 1)) % 2 ^ 256 = 2 ^ (63 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_63_lo :
    model_ln_wad_to_wad_evm (2 ^ (63 + 1) - 1) = 2914887881943677490 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (63 + 1) - 1) % 2 ^ 256 = 2 ^ (63 + 1) - 1 by decide]
  rw [ray_eval_seam_63_lo]
  decide

private theorem wad_eval_seam_63_hi :
    model_ln_wad_to_wad_evm (2 ^ (63 + 1)) = 2914887881943677490 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (63 + 1)) % 2 ^ 256 = 2 ^ (63 + 1) by decide]
  rw [ray_eval_seam_63_hi]
  decide

private theorem ray_seam_63 :
    sle (model_ln_wad_evm (2 ^ (63 + 1) - 1)) (model_ln_wad_evm (2 ^ (63 + 1))) = true := by
  rw [ray_eval_seam_63_lo, ray_eval_seam_63_hi]
  unfold sle
  decide

private theorem wad_seam_63 :
    sle (model_ln_wad_to_wad_evm (2 ^ (63 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (63 + 1))) = true := by
  rw [wad_eval_seam_63_lo, wad_eval_seam_63_hi]
  unfold sle
  decide

private theorem ray_eval_seam_64_lo :
    model_ln_wad_evm (2 ^ (64 + 1) - 1) = 3608035062503622799769136655 := by
  have hlog : Nat.log2 (2 ^ (64 + 1) - 1) = 64 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (64 + 1) - 1) % 2 ^ 256 = 2 ^ (64 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_64_hi :
    model_ln_wad_evm (2 ^ (64 + 1)) = 3608035062503622799796241710 := by
  have hlog : Nat.log2 (2 ^ (64 + 1)) = 65 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (64 + 1)) % 2 ^ 256 = 2 ^ (64 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_64_lo :
    model_ln_wad_to_wad_evm (2 ^ (64 + 1) - 1) = 3608035062503622799 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (64 + 1) - 1) % 2 ^ 256 = 2 ^ (64 + 1) - 1 by decide]
  rw [ray_eval_seam_64_lo]
  decide

private theorem wad_eval_seam_64_hi :
    model_ln_wad_to_wad_evm (2 ^ (64 + 1)) = 3608035062503622799 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (64 + 1)) % 2 ^ 256 = 2 ^ (64 + 1) by decide]
  rw [ray_eval_seam_64_hi]
  decide

private theorem ray_seam_64 :
    sle (model_ln_wad_evm (2 ^ (64 + 1) - 1)) (model_ln_wad_evm (2 ^ (64 + 1))) = true := by
  rw [ray_eval_seam_64_lo, ray_eval_seam_64_hi]
  unfold sle
  decide

private theorem wad_seam_64 :
    sle (model_ln_wad_to_wad_evm (2 ^ (64 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (64 + 1))) = true := by
  rw [wad_eval_seam_64_lo, wad_eval_seam_64_hi]
  unfold sle
  decide

private theorem ray_eval_seam_65_lo :
    model_ln_wad_evm (2 ^ (65 + 1) - 1) = 4301182243063568109199921304 := by
  have hlog : Nat.log2 (2 ^ (65 + 1) - 1) = 65 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (65 + 1) - 1) % 2 ^ 256 = 2 ^ (65 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_65_hi :
    model_ln_wad_evm (2 ^ (65 + 1)) = 4301182243063568109213473831 := by
  have hlog : Nat.log2 (2 ^ (65 + 1)) = 66 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (65 + 1)) % 2 ^ 256 = 2 ^ (65 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_65_lo :
    model_ln_wad_to_wad_evm (2 ^ (65 + 1) - 1) = 4301182243063568109 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (65 + 1) - 1) % 2 ^ 256 = 2 ^ (65 + 1) - 1 by decide]
  rw [ray_eval_seam_65_lo]
  decide

private theorem wad_eval_seam_65_hi :
    model_ln_wad_to_wad_evm (2 ^ (65 + 1)) = 4301182243063568109 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (65 + 1)) % 2 ^ 256 = 2 ^ (65 + 1) by decide]
  rw [ray_eval_seam_65_hi]
  decide

private theorem ray_seam_65 :
    sle (model_ln_wad_evm (2 ^ (65 + 1) - 1)) (model_ln_wad_evm (2 ^ (65 + 1))) = true := by
  rw [ray_eval_seam_65_lo, ray_eval_seam_65_hi]
  unfold sle
  decide

private theorem wad_seam_65 :
    sle (model_ln_wad_to_wad_evm (2 ^ (65 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (65 + 1))) = true := by
  rw [wad_eval_seam_65_lo, wad_eval_seam_65_hi]
  unfold sle
  decide

private theorem ray_eval_seam_66_lo :
    model_ln_wad_evm (2 ^ (66 + 1) - 1) = 4994329423623513418623929689 := by
  have hlog : Nat.log2 (2 ^ (66 + 1) - 1) = 66 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (66 + 1) - 1) % 2 ^ 256 = 2 ^ (66 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_66_hi :
    model_ln_wad_evm (2 ^ (66 + 1)) = 4994329423623513418630705953 := by
  have hlog : Nat.log2 (2 ^ (66 + 1)) = 67 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (66 + 1)) % 2 ^ 256 = 2 ^ (66 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_66_lo :
    model_ln_wad_to_wad_evm (2 ^ (66 + 1) - 1) = 4994329423623513418 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (66 + 1) - 1) % 2 ^ 256 = 2 ^ (66 + 1) - 1 by decide]
  rw [ray_eval_seam_66_lo]
  decide

private theorem wad_eval_seam_66_hi :
    model_ln_wad_to_wad_evm (2 ^ (66 + 1)) = 4994329423623513418 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (66 + 1)) % 2 ^ 256 = 2 ^ (66 + 1) by decide]
  rw [ray_eval_seam_66_hi]
  decide

private theorem ray_seam_66 :
    sle (model_ln_wad_evm (2 ^ (66 + 1) - 1)) (model_ln_wad_evm (2 ^ (66 + 1))) = true := by
  rw [ray_eval_seam_66_lo, ray_eval_seam_66_hi]
  unfold sle
  decide

private theorem wad_seam_66 :
    sle (model_ln_wad_to_wad_evm (2 ^ (66 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (66 + 1))) = true := by
  rw [wad_eval_seam_66_lo, wad_eval_seam_66_hi]
  unfold sle
  decide

private theorem ray_eval_seam_67_lo :
    model_ln_wad_evm (2 ^ (67 + 1) - 1) = 5687476604183458728044549942 := by
  have hlog : Nat.log2 (2 ^ (67 + 1) - 1) = 67 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (67 + 1) - 1) % 2 ^ 256 = 2 ^ (67 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_67_hi :
    model_ln_wad_evm (2 ^ (67 + 1)) = 5687476604183458728047938074 := by
  have hlog : Nat.log2 (2 ^ (67 + 1)) = 68 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (67 + 1)) % 2 ^ 256 = 2 ^ (67 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_67_lo :
    model_ln_wad_to_wad_evm (2 ^ (67 + 1) - 1) = 5687476604183458728 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (67 + 1) - 1) % 2 ^ 256 = 2 ^ (67 + 1) - 1 by decide]
  rw [ray_eval_seam_67_lo]
  decide

private theorem wad_eval_seam_67_hi :
    model_ln_wad_to_wad_evm (2 ^ (67 + 1)) = 5687476604183458728 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (67 + 1)) % 2 ^ 256 = 2 ^ (67 + 1) by decide]
  rw [ray_eval_seam_67_hi]
  decide

private theorem ray_seam_67 :
    sle (model_ln_wad_evm (2 ^ (67 + 1) - 1)) (model_ln_wad_evm (2 ^ (67 + 1))) = true := by
  rw [ray_eval_seam_67_lo, ray_eval_seam_67_hi]
  unfold sle
  decide

private theorem wad_seam_67 :
    sle (model_ln_wad_to_wad_evm (2 ^ (67 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (67 + 1))) = true := by
  rw [wad_eval_seam_67_lo, wad_eval_seam_67_hi]
  unfold sle
  decide

private theorem ray_eval_seam_68_lo :
    model_ln_wad_evm (2 ^ (68 + 1) - 1) = 6380623784743404037463476129 := by
  have hlog : Nat.log2 (2 ^ (68 + 1) - 1) = 68 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (68 + 1) - 1) % 2 ^ 256 = 2 ^ (68 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_68_hi :
    model_ln_wad_evm (2 ^ (68 + 1)) = 6380623784743404037465170196 := by
  have hlog : Nat.log2 (2 ^ (68 + 1)) = 69 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (68 + 1)) % 2 ^ 256 = 2 ^ (68 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_68_lo :
    model_ln_wad_to_wad_evm (2 ^ (68 + 1) - 1) = 6380623784743404037 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (68 + 1) - 1) % 2 ^ 256 = 2 ^ (68 + 1) - 1 by decide]
  rw [ray_eval_seam_68_lo]
  decide

private theorem wad_eval_seam_68_hi :
    model_ln_wad_to_wad_evm (2 ^ (68 + 1)) = 6380623784743404037 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (68 + 1)) % 2 ^ 256 = 2 ^ (68 + 1) by decide]
  rw [ray_eval_seam_68_hi]
  decide

private theorem ray_seam_68 :
    sle (model_ln_wad_evm (2 ^ (68 + 1) - 1)) (model_ln_wad_evm (2 ^ (68 + 1))) = true := by
  rw [ray_eval_seam_68_lo, ray_eval_seam_68_hi]
  unfold sle
  decide

private theorem wad_seam_68 :
    sle (model_ln_wad_to_wad_evm (2 ^ (68 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (68 + 1))) = true := by
  rw [wad_eval_seam_68_lo, wad_eval_seam_68_hi]
  unfold sle
  decide

private theorem ray_eval_seam_69_lo :
    model_ln_wad_evm (2 ^ (69 + 1) - 1) = 7073770965303349346881555284 := by
  have hlog : Nat.log2 (2 ^ (69 + 1) - 1) = 69 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (69 + 1) - 1) % 2 ^ 256 = 2 ^ (69 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_69_hi :
    model_ln_wad_evm (2 ^ (69 + 1)) = 7073770965303349346882402317 := by
  have hlog : Nat.log2 (2 ^ (69 + 1)) = 70 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (69 + 1)) % 2 ^ 256 = 2 ^ (69 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_69_lo :
    model_ln_wad_to_wad_evm (2 ^ (69 + 1) - 1) = 7073770965303349346 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (69 + 1) - 1) % 2 ^ 256 = 2 ^ (69 + 1) - 1 by decide]
  rw [ray_eval_seam_69_lo]
  decide

private theorem wad_eval_seam_69_hi :
    model_ln_wad_to_wad_evm (2 ^ (69 + 1)) = 7073770965303349346 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (69 + 1)) % 2 ^ 256 = 2 ^ (69 + 1) by decide]
  rw [ray_eval_seam_69_hi]
  decide

private theorem ray_seam_69 :
    sle (model_ln_wad_evm (2 ^ (69 + 1) - 1)) (model_ln_wad_evm (2 ^ (69 + 1))) = true := by
  rw [ray_eval_seam_69_lo, ray_eval_seam_69_hi]
  unfold sle
  decide

private theorem wad_seam_69 :
    sle (model_ln_wad_to_wad_evm (2 ^ (69 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (69 + 1))) = true := by
  rw [wad_eval_seam_69_lo, wad_eval_seam_69_hi]
  unfold sle
  decide

private theorem ray_eval_seam_70_lo :
    model_ln_wad_evm (2 ^ (70 + 1) - 1) = 7766918145863294656299210922 := by
  have hlog : Nat.log2 (2 ^ (70 + 1) - 1) = 70 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (70 + 1) - 1) % 2 ^ 256 = 2 ^ (70 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_70_hi :
    model_ln_wad_evm (2 ^ (70 + 1)) = 7766918145863294656299634439 := by
  have hlog : Nat.log2 (2 ^ (70 + 1)) = 71 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (70 + 1)) % 2 ^ 256 = 2 ^ (70 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_70_lo :
    model_ln_wad_to_wad_evm (2 ^ (70 + 1) - 1) = 7766918145863294656 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (70 + 1) - 1) % 2 ^ 256 = 2 ^ (70 + 1) - 1 by decide]
  rw [ray_eval_seam_70_lo]
  decide

private theorem wad_eval_seam_70_hi :
    model_ln_wad_to_wad_evm (2 ^ (70 + 1)) = 7766918145863294656 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (70 + 1)) % 2 ^ 256 = 2 ^ (70 + 1) by decide]
  rw [ray_eval_seam_70_hi]
  decide

private theorem ray_seam_70 :
    sle (model_ln_wad_evm (2 ^ (70 + 1) - 1)) (model_ln_wad_evm (2 ^ (70 + 1))) = true := by
  rw [ray_eval_seam_70_lo, ray_eval_seam_70_hi]
  unfold sle
  decide

private theorem wad_seam_70 :
    sle (model_ln_wad_to_wad_evm (2 ^ (70 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (70 + 1))) = true := by
  rw [wad_eval_seam_70_lo, wad_eval_seam_70_hi]
  unfold sle
  decide

private theorem ray_eval_seam_71_lo :
    model_ln_wad_evm (2 ^ (71 + 1) - 1) = 8460065326423239965716654801 := by
  have hlog : Nat.log2 (2 ^ (71 + 1) - 1) = 71 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (71 + 1) - 1) % 2 ^ 256 = 2 ^ (71 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_71_hi :
    model_ln_wad_evm (2 ^ (71 + 1)) = 8460065326423239965716866560 := by
  have hlog : Nat.log2 (2 ^ (71 + 1)) = 72 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (71 + 1)) % 2 ^ 256 = 2 ^ (71 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_71_lo :
    model_ln_wad_to_wad_evm (2 ^ (71 + 1) - 1) = 8460065326423239965 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (71 + 1) - 1) % 2 ^ 256 = 2 ^ (71 + 1) - 1 by decide]
  rw [ray_eval_seam_71_lo]
  decide

private theorem wad_eval_seam_71_hi :
    model_ln_wad_to_wad_evm (2 ^ (71 + 1)) = 8460065326423239965 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (71 + 1)) % 2 ^ 256 = 2 ^ (71 + 1) by decide]
  rw [ray_eval_seam_71_hi]
  decide

private theorem ray_seam_71 :
    sle (model_ln_wad_evm (2 ^ (71 + 1) - 1)) (model_ln_wad_evm (2 ^ (71 + 1))) = true := by
  rw [ray_eval_seam_71_lo, ray_eval_seam_71_hi]
  unfold sle
  decide

private theorem wad_seam_71 :
    sle (model_ln_wad_to_wad_evm (2 ^ (71 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (71 + 1))) = true := by
  rw [wad_eval_seam_71_lo, wad_eval_seam_71_hi]
  unfold sle
  decide

private theorem ray_eval_seam_72_lo :
    model_ln_wad_evm (2 ^ (72 + 1) - 1) = 9153212506983185275133992802 := by
  have hlog : Nat.log2 (2 ^ (72 + 1) - 1) = 72 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (72 + 1) - 1) % 2 ^ 256 = 2 ^ (72 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_72_hi :
    model_ln_wad_evm (2 ^ (72 + 1)) = 9153212506983185275134098682 := by
  have hlog : Nat.log2 (2 ^ (72 + 1)) = 73 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (72 + 1)) % 2 ^ 256 = 2 ^ (72 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_72_lo :
    model_ln_wad_to_wad_evm (2 ^ (72 + 1) - 1) = 9153212506983185275 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (72 + 1) - 1) % 2 ^ 256 = 2 ^ (72 + 1) - 1 by decide]
  rw [ray_eval_seam_72_lo]
  decide

private theorem wad_eval_seam_72_hi :
    model_ln_wad_to_wad_evm (2 ^ (72 + 1)) = 9153212506983185275 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (72 + 1)) % 2 ^ 256 = 2 ^ (72 + 1) by decide]
  rw [ray_eval_seam_72_hi]
  decide

private theorem ray_seam_72 :
    sle (model_ln_wad_evm (2 ^ (72 + 1) - 1)) (model_ln_wad_evm (2 ^ (72 + 1))) = true := by
  rw [ray_eval_seam_72_lo, ray_eval_seam_72_hi]
  unfold sle
  decide

private theorem wad_seam_72 :
    sle (model_ln_wad_to_wad_evm (2 ^ (72 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (72 + 1))) = true := by
  rw [wad_eval_seam_72_lo, wad_eval_seam_72_hi]
  unfold sle
  decide

private theorem ray_eval_seam_73_lo :
    model_ln_wad_evm (2 ^ (73 + 1) - 1) = 9846359687543130584551277863 := by
  have hlog : Nat.log2 (2 ^ (73 + 1) - 1) = 73 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (73 + 1) - 1) % 2 ^ 256 = 2 ^ (73 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_73_hi :
    model_ln_wad_evm (2 ^ (73 + 1)) = 9846359687543130584551330803 := by
  have hlog : Nat.log2 (2 ^ (73 + 1)) = 74 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (73 + 1)) % 2 ^ 256 = 2 ^ (73 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_73_lo :
    model_ln_wad_to_wad_evm (2 ^ (73 + 1) - 1) = 9846359687543130584 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (73 + 1) - 1) % 2 ^ 256 = 2 ^ (73 + 1) - 1 by decide]
  rw [ray_eval_seam_73_lo]
  decide

private theorem wad_eval_seam_73_hi :
    model_ln_wad_to_wad_evm (2 ^ (73 + 1)) = 9846359687543130584 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (73 + 1)) % 2 ^ 256 = 2 ^ (73 + 1) by decide]
  rw [ray_eval_seam_73_hi]
  decide

private theorem ray_seam_73 :
    sle (model_ln_wad_evm (2 ^ (73 + 1) - 1)) (model_ln_wad_evm (2 ^ (73 + 1))) = true := by
  rw [ray_eval_seam_73_lo, ray_eval_seam_73_hi]
  unfold sle
  decide

private theorem wad_seam_73 :
    sle (model_ln_wad_to_wad_evm (2 ^ (73 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (73 + 1))) = true := by
  rw [wad_eval_seam_73_lo, wad_eval_seam_73_hi]
  unfold sle
  decide

private theorem ray_eval_seam_74_lo :
    model_ln_wad_evm (2 ^ (74 + 1) - 1) = 10539506868103075893968536454 := by
  have hlog : Nat.log2 (2 ^ (74 + 1) - 1) = 74 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (74 + 1) - 1) % 2 ^ 256 = 2 ^ (74 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_74_hi :
    model_ln_wad_evm (2 ^ (74 + 1)) = 10539506868103075893968562925 := by
  have hlog : Nat.log2 (2 ^ (74 + 1)) = 75 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (74 + 1)) % 2 ^ 256 = 2 ^ (74 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_74_lo :
    model_ln_wad_to_wad_evm (2 ^ (74 + 1) - 1) = 10539506868103075893 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (74 + 1) - 1) % 2 ^ 256 = 2 ^ (74 + 1) - 1 by decide]
  rw [ray_eval_seam_74_lo]
  decide

private theorem wad_eval_seam_74_hi :
    model_ln_wad_to_wad_evm (2 ^ (74 + 1)) = 10539506868103075893 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (74 + 1)) % 2 ^ 256 = 2 ^ (74 + 1) by decide]
  rw [ray_eval_seam_74_hi]
  decide

private theorem ray_seam_74 :
    sle (model_ln_wad_evm (2 ^ (74 + 1) - 1)) (model_ln_wad_evm (2 ^ (74 + 1))) = true := by
  rw [ray_eval_seam_74_lo, ray_eval_seam_74_hi]
  unfold sle
  decide

private theorem wad_seam_74 :
    sle (model_ln_wad_to_wad_evm (2 ^ (74 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (74 + 1))) = true := by
  rw [wad_eval_seam_74_lo, wad_eval_seam_74_hi]
  unfold sle
  decide

private theorem ray_eval_seam_75_lo :
    model_ln_wad_evm (2 ^ (75 + 1) - 1) = 11232654048663021203385781810 := by
  have hlog : Nat.log2 (2 ^ (75 + 1) - 1) = 75 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (75 + 1) - 1) % 2 ^ 256 = 2 ^ (75 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_75_hi :
    model_ln_wad_evm (2 ^ (75 + 1)) = 11232654048663021203385795046 := by
  have hlog : Nat.log2 (2 ^ (75 + 1)) = 76 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (75 + 1)) % 2 ^ 256 = 2 ^ (75 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_75_lo :
    model_ln_wad_to_wad_evm (2 ^ (75 + 1) - 1) = 11232654048663021203 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (75 + 1) - 1) % 2 ^ 256 = 2 ^ (75 + 1) - 1 by decide]
  rw [ray_eval_seam_75_lo]
  decide

private theorem wad_eval_seam_75_hi :
    model_ln_wad_to_wad_evm (2 ^ (75 + 1)) = 11232654048663021203 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (75 + 1)) % 2 ^ 256 = 2 ^ (75 + 1) by decide]
  rw [ray_eval_seam_75_hi]
  decide

private theorem ray_seam_75 :
    sle (model_ln_wad_evm (2 ^ (75 + 1) - 1)) (model_ln_wad_evm (2 ^ (75 + 1))) = true := by
  rw [ray_eval_seam_75_lo, ray_eval_seam_75_hi]
  unfold sle
  decide

private theorem wad_seam_75 :
    sle (model_ln_wad_to_wad_evm (2 ^ (75 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (75 + 1))) = true := by
  rw [wad_eval_seam_75_lo, wad_eval_seam_75_hi]
  unfold sle
  decide

private theorem ray_eval_seam_76_lo :
    model_ln_wad_evm (2 ^ (76 + 1) - 1) = 11925801229222966512803020549 := by
  have hlog : Nat.log2 (2 ^ (76 + 1) - 1) = 76 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (76 + 1) - 1) % 2 ^ 256 = 2 ^ (76 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_76_hi :
    model_ln_wad_evm (2 ^ (76 + 1)) = 11925801229222966512803027167 := by
  have hlog : Nat.log2 (2 ^ (76 + 1)) = 77 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (76 + 1)) % 2 ^ 256 = 2 ^ (76 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_76_lo :
    model_ln_wad_to_wad_evm (2 ^ (76 + 1) - 1) = 11925801229222966512 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (76 + 1) - 1) % 2 ^ 256 = 2 ^ (76 + 1) - 1 by decide]
  rw [ray_eval_seam_76_lo]
  decide

private theorem wad_eval_seam_76_hi :
    model_ln_wad_to_wad_evm (2 ^ (76 + 1)) = 11925801229222966512 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (76 + 1)) % 2 ^ 256 = 2 ^ (76 + 1) by decide]
  rw [ray_eval_seam_76_hi]
  decide

private theorem ray_seam_76 :
    sle (model_ln_wad_evm (2 ^ (76 + 1) - 1)) (model_ln_wad_evm (2 ^ (76 + 1))) = true := by
  rw [ray_eval_seam_76_lo, ray_eval_seam_76_hi]
  unfold sle
  decide

private theorem wad_seam_76 :
    sle (model_ln_wad_to_wad_evm (2 ^ (76 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (76 + 1))) = true := by
  rw [wad_eval_seam_76_lo, wad_eval_seam_76_hi]
  unfold sle
  decide

private theorem ray_eval_seam_77_lo :
    model_ln_wad_evm (2 ^ (77 + 1) - 1) = 12618948409782911822220255980 := by
  have hlog : Nat.log2 (2 ^ (77 + 1) - 1) = 77 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (77 + 1) - 1) % 2 ^ 256 = 2 ^ (77 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_77_hi :
    model_ln_wad_evm (2 ^ (77 + 1)) = 12618948409782911822220259289 := by
  have hlog : Nat.log2 (2 ^ (77 + 1)) = 78 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (77 + 1)) % 2 ^ 256 = 2 ^ (77 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_77_lo :
    model_ln_wad_to_wad_evm (2 ^ (77 + 1) - 1) = 12618948409782911822 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (77 + 1) - 1) % 2 ^ 256 = 2 ^ (77 + 1) - 1 by decide]
  rw [ray_eval_seam_77_lo]
  decide

private theorem wad_eval_seam_77_hi :
    model_ln_wad_to_wad_evm (2 ^ (77 + 1)) = 12618948409782911822 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (77 + 1)) % 2 ^ 256 = 2 ^ (77 + 1) by decide]
  rw [ray_eval_seam_77_hi]
  decide

private theorem ray_seam_77 :
    sle (model_ln_wad_evm (2 ^ (77 + 1) - 1)) (model_ln_wad_evm (2 ^ (77 + 1))) = true := by
  rw [ray_eval_seam_77_lo, ray_eval_seam_77_hi]
  unfold sle
  decide

private theorem wad_seam_77 :
    sle (model_ln_wad_to_wad_evm (2 ^ (77 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (77 + 1))) = true := by
  rw [wad_eval_seam_77_lo, wad_eval_seam_77_hi]
  unfold sle
  decide

private theorem ray_eval_seam_78_lo :
    model_ln_wad_evm (2 ^ (78 + 1) - 1) = 13312095590342857131637489755 := by
  have hlog : Nat.log2 (2 ^ (78 + 1) - 1) = 78 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (78 + 1) - 1) % 2 ^ 256 = 2 ^ (78 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_78_hi :
    model_ln_wad_evm (2 ^ (78 + 1)) = 13312095590342857131637491410 := by
  have hlog : Nat.log2 (2 ^ (78 + 1)) = 79 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (78 + 1)) % 2 ^ 256 = 2 ^ (78 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_78_lo :
    model_ln_wad_to_wad_evm (2 ^ (78 + 1) - 1) = 13312095590342857131 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (78 + 1) - 1) % 2 ^ 256 = 2 ^ (78 + 1) - 1 by decide]
  rw [ray_eval_seam_78_lo]
  decide

private theorem wad_eval_seam_78_hi :
    model_ln_wad_to_wad_evm (2 ^ (78 + 1)) = 13312095590342857131 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (78 + 1)) % 2 ^ 256 = 2 ^ (78 + 1) by decide]
  rw [ray_eval_seam_78_hi]
  decide

private theorem ray_seam_78 :
    sle (model_ln_wad_evm (2 ^ (78 + 1) - 1)) (model_ln_wad_evm (2 ^ (78 + 1))) = true := by
  rw [ray_eval_seam_78_lo, ray_eval_seam_78_hi]
  unfold sle
  decide

private theorem wad_seam_78 :
    sle (model_ln_wad_to_wad_evm (2 ^ (78 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (78 + 1))) = true := by
  rw [wad_eval_seam_78_lo, wad_eval_seam_78_hi]
  unfold sle
  decide

private theorem ray_eval_seam_79_lo :
    model_ln_wad_evm (2 ^ (79 + 1) - 1) = 14005242770902802441054722704 := by
  have hlog : Nat.log2 (2 ^ (79 + 1) - 1) = 79 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (79 + 1) - 1) % 2 ^ 256 = 2 ^ (79 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_79_hi :
    model_ln_wad_evm (2 ^ (79 + 1)) = 14005242770902802441054723532 := by
  have hlog : Nat.log2 (2 ^ (79 + 1)) = 80 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (79 + 1)) % 2 ^ 256 = 2 ^ (79 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_79_lo :
    model_ln_wad_to_wad_evm (2 ^ (79 + 1) - 1) = 14005242770902802441 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (79 + 1) - 1) % 2 ^ 256 = 2 ^ (79 + 1) - 1 by decide]
  rw [ray_eval_seam_79_lo]
  decide

private theorem wad_eval_seam_79_hi :
    model_ln_wad_to_wad_evm (2 ^ (79 + 1)) = 14005242770902802441 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (79 + 1)) % 2 ^ 256 = 2 ^ (79 + 1) by decide]
  rw [ray_eval_seam_79_hi]
  decide

private theorem ray_seam_79 :
    sle (model_ln_wad_evm (2 ^ (79 + 1) - 1)) (model_ln_wad_evm (2 ^ (79 + 1))) = true := by
  rw [ray_eval_seam_79_lo, ray_eval_seam_79_hi]
  unfold sle
  decide

private theorem wad_seam_79 :
    sle (model_ln_wad_to_wad_evm (2 ^ (79 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (79 + 1))) = true := by
  rw [wad_eval_seam_79_lo, wad_eval_seam_79_hi]
  unfold sle
  decide

private theorem ray_eval_seam_80_lo :
    model_ln_wad_evm (2 ^ (80 + 1) - 1) = 14698389951462747750471955239 := by
  have hlog : Nat.log2 (2 ^ (80 + 1) - 1) = 80 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (80 + 1) - 1) % 2 ^ 256 = 2 ^ (80 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_80_hi :
    model_ln_wad_evm (2 ^ (80 + 1)) = 14698389951462747750471955653 := by
  have hlog : Nat.log2 (2 ^ (80 + 1)) = 81 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (80 + 1)) % 2 ^ 256 = 2 ^ (80 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_80_lo :
    model_ln_wad_to_wad_evm (2 ^ (80 + 1) - 1) = 14698389951462747750 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (80 + 1) - 1) % 2 ^ 256 = 2 ^ (80 + 1) - 1 by decide]
  rw [ray_eval_seam_80_lo]
  decide

private theorem wad_eval_seam_80_hi :
    model_ln_wad_to_wad_evm (2 ^ (80 + 1)) = 14698389951462747750 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (80 + 1)) % 2 ^ 256 = 2 ^ (80 + 1) by decide]
  rw [ray_eval_seam_80_hi]
  decide

private theorem ray_seam_80 :
    sle (model_ln_wad_evm (2 ^ (80 + 1) - 1)) (model_ln_wad_evm (2 ^ (80 + 1))) = true := by
  rw [ray_eval_seam_80_lo, ray_eval_seam_80_hi]
  unfold sle
  decide

private theorem wad_seam_80 :
    sle (model_ln_wad_to_wad_evm (2 ^ (80 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (80 + 1))) = true := by
  rw [wad_eval_seam_80_lo, wad_eval_seam_80_hi]
  unfold sle
  decide

private theorem ray_eval_seam_81_lo :
    model_ln_wad_evm (2 ^ (81 + 1) - 1) = 15391537132022693059889187567 := by
  have hlog : Nat.log2 (2 ^ (81 + 1) - 1) = 81 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (81 + 1) - 1) % 2 ^ 256 = 2 ^ (81 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_81_hi :
    model_ln_wad_evm (2 ^ (81 + 1)) = 15391537132022693059889187775 := by
  have hlog : Nat.log2 (2 ^ (81 + 1)) = 82 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (81 + 1)) % 2 ^ 256 = 2 ^ (81 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_81_lo :
    model_ln_wad_to_wad_evm (2 ^ (81 + 1) - 1) = 15391537132022693059 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (81 + 1) - 1) % 2 ^ 256 = 2 ^ (81 + 1) - 1 by decide]
  rw [ray_eval_seam_81_lo]
  decide

private theorem wad_eval_seam_81_hi :
    model_ln_wad_to_wad_evm (2 ^ (81 + 1)) = 15391537132022693059 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (81 + 1)) % 2 ^ 256 = 2 ^ (81 + 1) by decide]
  rw [ray_eval_seam_81_hi]
  decide

private theorem ray_seam_81 :
    sle (model_ln_wad_evm (2 ^ (81 + 1) - 1)) (model_ln_wad_evm (2 ^ (81 + 1))) = true := by
  rw [ray_eval_seam_81_lo, ray_eval_seam_81_hi]
  unfold sle
  decide

private theorem wad_seam_81 :
    sle (model_ln_wad_to_wad_evm (2 ^ (81 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (81 + 1))) = true := by
  rw [wad_eval_seam_81_lo, wad_eval_seam_81_hi]
  unfold sle
  decide

private theorem ray_eval_seam_82_lo :
    model_ln_wad_evm (2 ^ (82 + 1) - 1) = 16084684312582638369306419792 := by
  have hlog : Nat.log2 (2 ^ (82 + 1) - 1) = 82 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (82 + 1) - 1) % 2 ^ 256 = 2 ^ (82 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_82_hi :
    model_ln_wad_evm (2 ^ (82 + 1)) = 16084684312582638369306419896 := by
  have hlog : Nat.log2 (2 ^ (82 + 1)) = 83 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (82 + 1)) % 2 ^ 256 = 2 ^ (82 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_82_lo :
    model_ln_wad_to_wad_evm (2 ^ (82 + 1) - 1) = 16084684312582638369 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (82 + 1) - 1) % 2 ^ 256 = 2 ^ (82 + 1) - 1 by decide]
  rw [ray_eval_seam_82_lo]
  decide

private theorem wad_eval_seam_82_hi :
    model_ln_wad_to_wad_evm (2 ^ (82 + 1)) = 16084684312582638369 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (82 + 1)) % 2 ^ 256 = 2 ^ (82 + 1) by decide]
  rw [ray_eval_seam_82_hi]
  decide

private theorem ray_seam_82 :
    sle (model_ln_wad_evm (2 ^ (82 + 1) - 1)) (model_ln_wad_evm (2 ^ (82 + 1))) = true := by
  rw [ray_eval_seam_82_lo, ray_eval_seam_82_hi]
  unfold sle
  decide

private theorem wad_seam_82 :
    sle (model_ln_wad_to_wad_evm (2 ^ (82 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (82 + 1))) = true := by
  rw [wad_eval_seam_82_lo, wad_eval_seam_82_hi]
  unfold sle
  decide

private theorem ray_eval_seam_83_lo :
    model_ln_wad_evm (2 ^ (83 + 1) - 1) = 16777831493142583678723651965 := by
  have hlog : Nat.log2 (2 ^ (83 + 1) - 1) = 83 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (83 + 1) - 1) % 2 ^ 256 = 2 ^ (83 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_83_hi :
    model_ln_wad_evm (2 ^ (83 + 1)) = 16777831493142583678723652018 := by
  have hlog : Nat.log2 (2 ^ (83 + 1)) = 84 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (83 + 1)) % 2 ^ 256 = 2 ^ (83 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_83_lo :
    model_ln_wad_to_wad_evm (2 ^ (83 + 1) - 1) = 16777831493142583678 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (83 + 1) - 1) % 2 ^ 256 = 2 ^ (83 + 1) - 1 by decide]
  rw [ray_eval_seam_83_lo]
  decide

private theorem wad_eval_seam_83_hi :
    model_ln_wad_to_wad_evm (2 ^ (83 + 1)) = 16777831493142583678 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (83 + 1)) % 2 ^ 256 = 2 ^ (83 + 1) by decide]
  rw [ray_eval_seam_83_hi]
  decide

private theorem ray_seam_83 :
    sle (model_ln_wad_evm (2 ^ (83 + 1) - 1)) (model_ln_wad_evm (2 ^ (83 + 1))) = true := by
  rw [ray_eval_seam_83_lo, ray_eval_seam_83_hi]
  unfold sle
  decide

private theorem wad_seam_83 :
    sle (model_ln_wad_to_wad_evm (2 ^ (83 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (83 + 1))) = true := by
  rw [wad_eval_seam_83_lo, wad_eval_seam_83_hi]
  unfold sle
  decide

private theorem ray_eval_seam_84_lo :
    model_ln_wad_evm (2 ^ (84 + 1) - 1) = 17470978673702528988140884113 := by
  have hlog : Nat.log2 (2 ^ (84 + 1) - 1) = 84 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (84 + 1) - 1) % 2 ^ 256 = 2 ^ (84 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_84_hi :
    model_ln_wad_evm (2 ^ (84 + 1)) = 17470978673702528988140884139 := by
  have hlog : Nat.log2 (2 ^ (84 + 1)) = 85 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (84 + 1)) % 2 ^ 256 = 2 ^ (84 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_84_lo :
    model_ln_wad_to_wad_evm (2 ^ (84 + 1) - 1) = 17470978673702528988 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (84 + 1) - 1) % 2 ^ 256 = 2 ^ (84 + 1) - 1 by decide]
  rw [ray_eval_seam_84_lo]
  decide

private theorem wad_eval_seam_84_hi :
    model_ln_wad_to_wad_evm (2 ^ (84 + 1)) = 17470978673702528988 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (84 + 1)) % 2 ^ 256 = 2 ^ (84 + 1) by decide]
  rw [ray_eval_seam_84_hi]
  decide

private theorem ray_seam_84 :
    sle (model_ln_wad_evm (2 ^ (84 + 1) - 1)) (model_ln_wad_evm (2 ^ (84 + 1))) = true := by
  rw [ray_eval_seam_84_lo, ray_eval_seam_84_hi]
  unfold sle
  decide

private theorem wad_seam_84 :
    sle (model_ln_wad_to_wad_evm (2 ^ (84 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (84 + 1))) = true := by
  rw [wad_eval_seam_84_lo, wad_eval_seam_84_hi]
  unfold sle
  decide

private theorem ray_eval_seam_85_lo :
    model_ln_wad_evm (2 ^ (85 + 1) - 1) = 18164125854262474297558116247 := by
  have hlog : Nat.log2 (2 ^ (85 + 1) - 1) = 85 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (85 + 1) - 1) % 2 ^ 256 = 2 ^ (85 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_85_hi :
    model_ln_wad_evm (2 ^ (85 + 1)) = 18164125854262474297558116261 := by
  have hlog : Nat.log2 (2 ^ (85 + 1)) = 86 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (85 + 1)) % 2 ^ 256 = 2 ^ (85 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_85_lo :
    model_ln_wad_to_wad_evm (2 ^ (85 + 1) - 1) = 18164125854262474297 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (85 + 1) - 1) % 2 ^ 256 = 2 ^ (85 + 1) - 1 by decide]
  rw [ray_eval_seam_85_lo]
  decide

private theorem wad_eval_seam_85_hi :
    model_ln_wad_to_wad_evm (2 ^ (85 + 1)) = 18164125854262474297 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (85 + 1)) % 2 ^ 256 = 2 ^ (85 + 1) by decide]
  rw [ray_eval_seam_85_hi]
  decide

private theorem ray_seam_85 :
    sle (model_ln_wad_evm (2 ^ (85 + 1) - 1)) (model_ln_wad_evm (2 ^ (85 + 1))) = true := by
  rw [ray_eval_seam_85_lo, ray_eval_seam_85_hi]
  unfold sle
  decide

private theorem wad_seam_85 :
    sle (model_ln_wad_to_wad_evm (2 ^ (85 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (85 + 1))) = true := by
  rw [wad_eval_seam_85_lo, wad_eval_seam_85_hi]
  unfold sle
  decide

private theorem ray_eval_seam_86_lo :
    model_ln_wad_evm (2 ^ (86 + 1) - 1) = 18857273034822419606975348375 := by
  have hlog : Nat.log2 (2 ^ (86 + 1) - 1) = 86 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (86 + 1) - 1) % 2 ^ 256 = 2 ^ (86 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_86_hi :
    model_ln_wad_evm (2 ^ (86 + 1)) = 18857273034822419606975348382 := by
  have hlog : Nat.log2 (2 ^ (86 + 1)) = 87 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (86 + 1)) % 2 ^ 256 = 2 ^ (86 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_86_lo :
    model_ln_wad_to_wad_evm (2 ^ (86 + 1) - 1) = 18857273034822419606 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (86 + 1) - 1) % 2 ^ 256 = 2 ^ (86 + 1) - 1 by decide]
  rw [ray_eval_seam_86_lo]
  decide

private theorem wad_eval_seam_86_hi :
    model_ln_wad_to_wad_evm (2 ^ (86 + 1)) = 18857273034822419606 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (86 + 1)) % 2 ^ 256 = 2 ^ (86 + 1) by decide]
  rw [ray_eval_seam_86_hi]
  decide

private theorem ray_seam_86 :
    sle (model_ln_wad_evm (2 ^ (86 + 1) - 1)) (model_ln_wad_evm (2 ^ (86 + 1))) = true := by
  rw [ray_eval_seam_86_lo, ray_eval_seam_86_hi]
  unfold sle
  decide

private theorem wad_seam_86 :
    sle (model_ln_wad_to_wad_evm (2 ^ (86 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (86 + 1))) = true := by
  rw [wad_eval_seam_86_lo, wad_eval_seam_86_hi]
  unfold sle
  decide

private theorem ray_eval_seam_87_lo :
    model_ln_wad_evm (2 ^ (87 + 1) - 1) = 19550420215382364916392580500 := by
  have hlog : Nat.log2 (2 ^ (87 + 1) - 1) = 87 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (87 + 1) - 1) % 2 ^ 256 = 2 ^ (87 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_87_hi :
    model_ln_wad_evm (2 ^ (87 + 1)) = 19550420215382364916392580503 := by
  have hlog : Nat.log2 (2 ^ (87 + 1)) = 88 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (87 + 1)) % 2 ^ 256 = 2 ^ (87 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_87_lo :
    model_ln_wad_to_wad_evm (2 ^ (87 + 1) - 1) = 19550420215382364916 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (87 + 1) - 1) % 2 ^ 256 = 2 ^ (87 + 1) - 1 by decide]
  rw [ray_eval_seam_87_lo]
  decide

private theorem wad_eval_seam_87_hi :
    model_ln_wad_to_wad_evm (2 ^ (87 + 1)) = 19550420215382364916 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (87 + 1)) % 2 ^ 256 = 2 ^ (87 + 1) by decide]
  rw [ray_eval_seam_87_hi]
  decide

private theorem ray_seam_87 :
    sle (model_ln_wad_evm (2 ^ (87 + 1) - 1)) (model_ln_wad_evm (2 ^ (87 + 1))) = true := by
  rw [ray_eval_seam_87_lo, ray_eval_seam_87_hi]
  unfold sle
  decide

private theorem wad_seam_87 :
    sle (model_ln_wad_to_wad_evm (2 ^ (87 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (87 + 1))) = true := by
  rw [wad_eval_seam_87_lo, wad_eval_seam_87_hi]
  unfold sle
  decide

private theorem ray_eval_seam_88_lo :
    model_ln_wad_evm (2 ^ (88 + 1) - 1) = 20243567395942310225809812623 := by
  have hlog : Nat.log2 (2 ^ (88 + 1) - 1) = 88 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (88 + 1) - 1) % 2 ^ 256 = 2 ^ (88 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_88_hi :
    model_ln_wad_evm (2 ^ (88 + 1)) = 20243567395942310225809812625 := by
  have hlog : Nat.log2 (2 ^ (88 + 1)) = 89 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (88 + 1)) % 2 ^ 256 = 2 ^ (88 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_88_lo :
    model_ln_wad_to_wad_evm (2 ^ (88 + 1) - 1) = 20243567395942310225 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (88 + 1) - 1) % 2 ^ 256 = 2 ^ (88 + 1) - 1 by decide]
  rw [ray_eval_seam_88_lo]
  decide

private theorem wad_eval_seam_88_hi :
    model_ln_wad_to_wad_evm (2 ^ (88 + 1)) = 20243567395942310225 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (88 + 1)) % 2 ^ 256 = 2 ^ (88 + 1) by decide]
  rw [ray_eval_seam_88_hi]
  decide

private theorem ray_seam_88 :
    sle (model_ln_wad_evm (2 ^ (88 + 1) - 1)) (model_ln_wad_evm (2 ^ (88 + 1))) = true := by
  rw [ray_eval_seam_88_lo, ray_eval_seam_88_hi]
  unfold sle
  decide

private theorem wad_seam_88 :
    sle (model_ln_wad_to_wad_evm (2 ^ (88 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (88 + 1))) = true := by
  rw [wad_eval_seam_88_lo, wad_eval_seam_88_hi]
  unfold sle
  decide

private theorem ray_eval_seam_89_lo :
    model_ln_wad_evm (2 ^ (89 + 1) - 1) = 20936714576502255535227044745 := by
  have hlog : Nat.log2 (2 ^ (89 + 1) - 1) = 89 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (89 + 1) - 1) % 2 ^ 256 = 2 ^ (89 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_89_hi :
    model_ln_wad_evm (2 ^ (89 + 1)) = 20936714576502255535227044746 := by
  have hlog : Nat.log2 (2 ^ (89 + 1)) = 90 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (89 + 1)) % 2 ^ 256 = 2 ^ (89 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_89_lo :
    model_ln_wad_to_wad_evm (2 ^ (89 + 1) - 1) = 20936714576502255535 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (89 + 1) - 1) % 2 ^ 256 = 2 ^ (89 + 1) - 1 by decide]
  rw [ray_eval_seam_89_lo]
  decide

private theorem wad_eval_seam_89_hi :
    model_ln_wad_to_wad_evm (2 ^ (89 + 1)) = 20936714576502255535 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (89 + 1)) % 2 ^ 256 = 2 ^ (89 + 1) by decide]
  rw [ray_eval_seam_89_hi]
  decide

private theorem ray_seam_89 :
    sle (model_ln_wad_evm (2 ^ (89 + 1) - 1)) (model_ln_wad_evm (2 ^ (89 + 1))) = true := by
  rw [ray_eval_seam_89_lo, ray_eval_seam_89_hi]
  unfold sle
  decide

private theorem wad_seam_89 :
    sle (model_ln_wad_to_wad_evm (2 ^ (89 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (89 + 1))) = true := by
  rw [wad_eval_seam_89_lo, wad_eval_seam_89_hi]
  unfold sle
  decide

private theorem ray_eval_seam_90_lo :
    model_ln_wad_evm (2 ^ (90 + 1) - 1) = 21629861757062200844644276867 := by
  have hlog : Nat.log2 (2 ^ (90 + 1) - 1) = 90 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (90 + 1) - 1) % 2 ^ 256 = 2 ^ (90 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_90_hi :
    model_ln_wad_evm (2 ^ (90 + 1)) = 21629861757062200844644276868 := by
  have hlog : Nat.log2 (2 ^ (90 + 1)) = 91 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (90 + 1)) % 2 ^ 256 = 2 ^ (90 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_90_lo :
    model_ln_wad_to_wad_evm (2 ^ (90 + 1) - 1) = 21629861757062200844 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (90 + 1) - 1) % 2 ^ 256 = 2 ^ (90 + 1) - 1 by decide]
  rw [ray_eval_seam_90_lo]
  decide

private theorem wad_eval_seam_90_hi :
    model_ln_wad_to_wad_evm (2 ^ (90 + 1)) = 21629861757062200844 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (90 + 1)) % 2 ^ 256 = 2 ^ (90 + 1) by decide]
  rw [ray_eval_seam_90_hi]
  decide

private theorem ray_seam_90 :
    sle (model_ln_wad_evm (2 ^ (90 + 1) - 1)) (model_ln_wad_evm (2 ^ (90 + 1))) = true := by
  rw [ray_eval_seam_90_lo, ray_eval_seam_90_hi]
  unfold sle
  decide

private theorem wad_seam_90 :
    sle (model_ln_wad_to_wad_evm (2 ^ (90 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (90 + 1))) = true := by
  rw [wad_eval_seam_90_lo, wad_eval_seam_90_hi]
  unfold sle
  decide

private theorem ray_eval_seam_91_lo :
    model_ln_wad_evm (2 ^ (91 + 1) - 1) = 22323008937622146154061508988 := by
  have hlog : Nat.log2 (2 ^ (91 + 1) - 1) = 91 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (91 + 1) - 1) % 2 ^ 256 = 2 ^ (91 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_91_hi :
    model_ln_wad_evm (2 ^ (91 + 1)) = 22323008937622146154061508989 := by
  have hlog : Nat.log2 (2 ^ (91 + 1)) = 92 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (91 + 1)) % 2 ^ 256 = 2 ^ (91 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_91_lo :
    model_ln_wad_to_wad_evm (2 ^ (91 + 1) - 1) = 22323008937622146154 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (91 + 1) - 1) % 2 ^ 256 = 2 ^ (91 + 1) - 1 by decide]
  rw [ray_eval_seam_91_lo]
  decide

private theorem wad_eval_seam_91_hi :
    model_ln_wad_to_wad_evm (2 ^ (91 + 1)) = 22323008937622146154 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (91 + 1)) % 2 ^ 256 = 2 ^ (91 + 1) by decide]
  rw [ray_eval_seam_91_hi]
  decide

private theorem ray_seam_91 :
    sle (model_ln_wad_evm (2 ^ (91 + 1) - 1)) (model_ln_wad_evm (2 ^ (91 + 1))) = true := by
  rw [ray_eval_seam_91_lo, ray_eval_seam_91_hi]
  unfold sle
  decide

private theorem wad_seam_91 :
    sle (model_ln_wad_to_wad_evm (2 ^ (91 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (91 + 1))) = true := by
  rw [wad_eval_seam_91_lo, wad_eval_seam_91_hi]
  unfold sle
  decide

private theorem ray_eval_seam_92_lo :
    model_ln_wad_evm (2 ^ (92 + 1) - 1) = 23016156118182091463478741110 := by
  have hlog : Nat.log2 (2 ^ (92 + 1) - 1) = 92 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (92 + 1) - 1) % 2 ^ 256 = 2 ^ (92 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_92_hi :
    model_ln_wad_evm (2 ^ (92 + 1)) = 23016156118182091463478741111 := by
  have hlog : Nat.log2 (2 ^ (92 + 1)) = 93 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (92 + 1)) % 2 ^ 256 = 2 ^ (92 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_92_lo :
    model_ln_wad_to_wad_evm (2 ^ (92 + 1) - 1) = 23016156118182091463 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (92 + 1) - 1) % 2 ^ 256 = 2 ^ (92 + 1) - 1 by decide]
  rw [ray_eval_seam_92_lo]
  decide

private theorem wad_eval_seam_92_hi :
    model_ln_wad_to_wad_evm (2 ^ (92 + 1)) = 23016156118182091463 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (92 + 1)) % 2 ^ 256 = 2 ^ (92 + 1) by decide]
  rw [ray_eval_seam_92_hi]
  decide

private theorem ray_seam_92 :
    sle (model_ln_wad_evm (2 ^ (92 + 1) - 1)) (model_ln_wad_evm (2 ^ (92 + 1))) = true := by
  rw [ray_eval_seam_92_lo, ray_eval_seam_92_hi]
  unfold sle
  decide

private theorem wad_seam_92 :
    sle (model_ln_wad_to_wad_evm (2 ^ (92 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (92 + 1))) = true := by
  rw [wad_eval_seam_92_lo, wad_eval_seam_92_hi]
  unfold sle
  decide

private theorem ray_eval_seam_93_lo :
    model_ln_wad_evm (2 ^ (93 + 1) - 1) = 23709303298742036772895973232 := by
  have hlog : Nat.log2 (2 ^ (93 + 1) - 1) = 93 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (93 + 1) - 1) % 2 ^ 256 = 2 ^ (93 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_93_hi :
    model_ln_wad_evm (2 ^ (93 + 1)) = 23709303298742036772895973232 := by
  have hlog : Nat.log2 (2 ^ (93 + 1)) = 94 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (93 + 1)) % 2 ^ 256 = 2 ^ (93 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_93_lo :
    model_ln_wad_to_wad_evm (2 ^ (93 + 1) - 1) = 23709303298742036772 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (93 + 1) - 1) % 2 ^ 256 = 2 ^ (93 + 1) - 1 by decide]
  rw [ray_eval_seam_93_lo]
  decide

private theorem wad_eval_seam_93_hi :
    model_ln_wad_to_wad_evm (2 ^ (93 + 1)) = 23709303298742036772 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (93 + 1)) % 2 ^ 256 = 2 ^ (93 + 1) by decide]
  rw [ray_eval_seam_93_hi]
  decide

private theorem ray_seam_93 :
    sle (model_ln_wad_evm (2 ^ (93 + 1) - 1)) (model_ln_wad_evm (2 ^ (93 + 1))) = true := by
  rw [ray_eval_seam_93_lo, ray_eval_seam_93_hi]
  unfold sle
  decide

private theorem wad_seam_93 :
    sle (model_ln_wad_to_wad_evm (2 ^ (93 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (93 + 1))) = true := by
  rw [wad_eval_seam_93_lo, wad_eval_seam_93_hi]
  unfold sle
  decide

private theorem ray_eval_seam_94_lo :
    model_ln_wad_evm (2 ^ (94 + 1) - 1) = 24402450479301982082313205353 := by
  have hlog : Nat.log2 (2 ^ (94 + 1) - 1) = 94 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (94 + 1) - 1) % 2 ^ 256 = 2 ^ (94 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_94_hi :
    model_ln_wad_evm (2 ^ (94 + 1)) = 24402450479301982082313205354 := by
  have hlog : Nat.log2 (2 ^ (94 + 1)) = 95 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (94 + 1)) % 2 ^ 256 = 2 ^ (94 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_94_lo :
    model_ln_wad_to_wad_evm (2 ^ (94 + 1) - 1) = 24402450479301982082 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (94 + 1) - 1) % 2 ^ 256 = 2 ^ (94 + 1) - 1 by decide]
  rw [ray_eval_seam_94_lo]
  decide

private theorem wad_eval_seam_94_hi :
    model_ln_wad_to_wad_evm (2 ^ (94 + 1)) = 24402450479301982082 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (94 + 1)) % 2 ^ 256 = 2 ^ (94 + 1) by decide]
  rw [ray_eval_seam_94_hi]
  decide

private theorem ray_seam_94 :
    sle (model_ln_wad_evm (2 ^ (94 + 1) - 1)) (model_ln_wad_evm (2 ^ (94 + 1))) = true := by
  rw [ray_eval_seam_94_lo, ray_eval_seam_94_hi]
  unfold sle
  decide

private theorem wad_seam_94 :
    sle (model_ln_wad_to_wad_evm (2 ^ (94 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (94 + 1))) = true := by
  rw [wad_eval_seam_94_lo, wad_eval_seam_94_hi]
  unfold sle
  decide

private theorem ray_eval_seam_95_lo :
    model_ln_wad_evm (2 ^ (95 + 1) - 1) = 25095597659861927391730437474 := by
  have hlog : Nat.log2 (2 ^ (95 + 1) - 1) = 95 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (95 + 1) - 1) % 2 ^ 256 = 2 ^ (95 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_95_hi :
    model_ln_wad_evm (2 ^ (95 + 1)) = 25095597659861927391730437475 := by
  have hlog : Nat.log2 (2 ^ (95 + 1)) = 96 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (95 + 1)) % 2 ^ 256 = 2 ^ (95 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_95_lo :
    model_ln_wad_to_wad_evm (2 ^ (95 + 1) - 1) = 25095597659861927391 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (95 + 1) - 1) % 2 ^ 256 = 2 ^ (95 + 1) - 1 by decide]
  rw [ray_eval_seam_95_lo]
  decide

private theorem wad_eval_seam_95_hi :
    model_ln_wad_to_wad_evm (2 ^ (95 + 1)) = 25095597659861927391 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (95 + 1)) % 2 ^ 256 = 2 ^ (95 + 1) by decide]
  rw [ray_eval_seam_95_hi]
  decide

private theorem ray_seam_95 :
    sle (model_ln_wad_evm (2 ^ (95 + 1) - 1)) (model_ln_wad_evm (2 ^ (95 + 1))) = true := by
  rw [ray_eval_seam_95_lo, ray_eval_seam_95_hi]
  unfold sle
  decide

private theorem wad_seam_95 :
    sle (model_ln_wad_to_wad_evm (2 ^ (95 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (95 + 1))) = true := by
  rw [wad_eval_seam_95_lo, wad_eval_seam_95_hi]
  unfold sle
  decide

private theorem ray_eval_seam_96_lo :
    model_ln_wad_evm (2 ^ (96 + 1) - 1) = 25788744840421872701147669596 := by
  have hlog : Nat.log2 (2 ^ (96 + 1) - 1) = 96 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (96 + 1) - 1) % 2 ^ 256 = 2 ^ (96 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_96_hi :
    model_ln_wad_evm (2 ^ (96 + 1)) = 25788744840421872701147669597 := by
  have hlog : Nat.log2 (2 ^ (96 + 1)) = 97 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (96 + 1)) % 2 ^ 256 = 2 ^ (96 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_96_lo :
    model_ln_wad_to_wad_evm (2 ^ (96 + 1) - 1) = 25788744840421872701 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (96 + 1) - 1) % 2 ^ 256 = 2 ^ (96 + 1) - 1 by decide]
  rw [ray_eval_seam_96_lo]
  decide

private theorem wad_eval_seam_96_hi :
    model_ln_wad_to_wad_evm (2 ^ (96 + 1)) = 25788744840421872701 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (96 + 1)) % 2 ^ 256 = 2 ^ (96 + 1) by decide]
  rw [ray_eval_seam_96_hi]
  decide

private theorem ray_seam_96 :
    sle (model_ln_wad_evm (2 ^ (96 + 1) - 1)) (model_ln_wad_evm (2 ^ (96 + 1))) = true := by
  rw [ray_eval_seam_96_lo, ray_eval_seam_96_hi]
  unfold sle
  decide

private theorem wad_seam_96 :
    sle (model_ln_wad_to_wad_evm (2 ^ (96 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (96 + 1))) = true := by
  rw [wad_eval_seam_96_lo, wad_eval_seam_96_hi]
  unfold sle
  decide

private theorem ray_eval_seam_97_lo :
    model_ln_wad_evm (2 ^ (97 + 1) - 1) = 26481892020981818010564901717 := by
  have hlog : Nat.log2 (2 ^ (97 + 1) - 1) = 97 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (97 + 1) - 1) % 2 ^ 256 = 2 ^ (97 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_97_hi :
    model_ln_wad_evm (2 ^ (97 + 1)) = 26481892020981818010564901718 := by
  have hlog : Nat.log2 (2 ^ (97 + 1)) = 98 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (97 + 1)) % 2 ^ 256 = 2 ^ (97 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_97_lo :
    model_ln_wad_to_wad_evm (2 ^ (97 + 1) - 1) = 26481892020981818010 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (97 + 1) - 1) % 2 ^ 256 = 2 ^ (97 + 1) - 1 by decide]
  rw [ray_eval_seam_97_lo]
  decide

private theorem wad_eval_seam_97_hi :
    model_ln_wad_to_wad_evm (2 ^ (97 + 1)) = 26481892020981818010 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (97 + 1)) % 2 ^ 256 = 2 ^ (97 + 1) by decide]
  rw [ray_eval_seam_97_hi]
  decide

private theorem ray_seam_97 :
    sle (model_ln_wad_evm (2 ^ (97 + 1) - 1)) (model_ln_wad_evm (2 ^ (97 + 1))) = true := by
  rw [ray_eval_seam_97_lo, ray_eval_seam_97_hi]
  unfold sle
  decide

private theorem wad_seam_97 :
    sle (model_ln_wad_to_wad_evm (2 ^ (97 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (97 + 1))) = true := by
  rw [wad_eval_seam_97_lo, wad_eval_seam_97_hi]
  unfold sle
  decide

private theorem ray_eval_seam_98_lo :
    model_ln_wad_evm (2 ^ (98 + 1) - 1) = 27175039201541763319982133839 := by
  have hlog : Nat.log2 (2 ^ (98 + 1) - 1) = 98 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (98 + 1) - 1) % 2 ^ 256 = 2 ^ (98 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_98_hi :
    model_ln_wad_evm (2 ^ (98 + 1)) = 27175039201541763319982133840 := by
  have hlog : Nat.log2 (2 ^ (98 + 1)) = 99 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (98 + 1)) % 2 ^ 256 = 2 ^ (98 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_98_lo :
    model_ln_wad_to_wad_evm (2 ^ (98 + 1) - 1) = 27175039201541763319 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (98 + 1) - 1) % 2 ^ 256 = 2 ^ (98 + 1) - 1 by decide]
  rw [ray_eval_seam_98_lo]
  decide

private theorem wad_eval_seam_98_hi :
    model_ln_wad_to_wad_evm (2 ^ (98 + 1)) = 27175039201541763319 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (98 + 1)) % 2 ^ 256 = 2 ^ (98 + 1) by decide]
  rw [ray_eval_seam_98_hi]
  decide

private theorem ray_seam_98 :
    sle (model_ln_wad_evm (2 ^ (98 + 1) - 1)) (model_ln_wad_evm (2 ^ (98 + 1))) = true := by
  rw [ray_eval_seam_98_lo, ray_eval_seam_98_hi]
  unfold sle
  decide

private theorem wad_seam_98 :
    sle (model_ln_wad_to_wad_evm (2 ^ (98 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (98 + 1))) = true := by
  rw [wad_eval_seam_98_lo, wad_eval_seam_98_hi]
  unfold sle
  decide

private theorem ray_eval_seam_99_lo :
    model_ln_wad_evm (2 ^ (99 + 1) - 1) = 27868186382101708629399365960 := by
  have hlog : Nat.log2 (2 ^ (99 + 1) - 1) = 99 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (99 + 1) - 1) % 2 ^ 256 = 2 ^ (99 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_99_hi :
    model_ln_wad_evm (2 ^ (99 + 1)) = 27868186382101708629399365961 := by
  have hlog : Nat.log2 (2 ^ (99 + 1)) = 100 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (99 + 1)) % 2 ^ 256 = 2 ^ (99 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_99_lo :
    model_ln_wad_to_wad_evm (2 ^ (99 + 1) - 1) = 27868186382101708629 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (99 + 1) - 1) % 2 ^ 256 = 2 ^ (99 + 1) - 1 by decide]
  rw [ray_eval_seam_99_lo]
  decide

private theorem wad_eval_seam_99_hi :
    model_ln_wad_to_wad_evm (2 ^ (99 + 1)) = 27868186382101708629 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (99 + 1)) % 2 ^ 256 = 2 ^ (99 + 1) by decide]
  rw [ray_eval_seam_99_hi]
  decide

private theorem ray_seam_99 :
    sle (model_ln_wad_evm (2 ^ (99 + 1) - 1)) (model_ln_wad_evm (2 ^ (99 + 1))) = true := by
  rw [ray_eval_seam_99_lo, ray_eval_seam_99_hi]
  unfold sle
  decide

private theorem wad_seam_99 :
    sle (model_ln_wad_to_wad_evm (2 ^ (99 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (99 + 1))) = true := by
  rw [wad_eval_seam_99_lo, wad_eval_seam_99_hi]
  unfold sle
  decide

private theorem ray_eval_seam_100_lo :
    model_ln_wad_evm (2 ^ (100 + 1) - 1) = 28561333562661653938816598082 := by
  have hlog : Nat.log2 (2 ^ (100 + 1) - 1) = 100 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (100 + 1) - 1) % 2 ^ 256 = 2 ^ (100 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_100_hi :
    model_ln_wad_evm (2 ^ (100 + 1)) = 28561333562661653938816598082 := by
  have hlog : Nat.log2 (2 ^ (100 + 1)) = 101 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (100 + 1)) % 2 ^ 256 = 2 ^ (100 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_100_lo :
    model_ln_wad_to_wad_evm (2 ^ (100 + 1) - 1) = 28561333562661653938 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (100 + 1) - 1) % 2 ^ 256 = 2 ^ (100 + 1) - 1 by decide]
  rw [ray_eval_seam_100_lo]
  decide

private theorem wad_eval_seam_100_hi :
    model_ln_wad_to_wad_evm (2 ^ (100 + 1)) = 28561333562661653938 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (100 + 1)) % 2 ^ 256 = 2 ^ (100 + 1) by decide]
  rw [ray_eval_seam_100_hi]
  decide

private theorem ray_seam_100 :
    sle (model_ln_wad_evm (2 ^ (100 + 1) - 1)) (model_ln_wad_evm (2 ^ (100 + 1))) = true := by
  rw [ray_eval_seam_100_lo, ray_eval_seam_100_hi]
  unfold sle
  decide

private theorem wad_seam_100 :
    sle (model_ln_wad_to_wad_evm (2 ^ (100 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (100 + 1))) = true := by
  rw [wad_eval_seam_100_lo, wad_eval_seam_100_hi]
  unfold sle
  decide

private theorem ray_eval_seam_101_lo :
    model_ln_wad_evm (2 ^ (101 + 1) - 1) = 29254480743221599248233830203 := by
  have hlog : Nat.log2 (2 ^ (101 + 1) - 1) = 101 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (101 + 1) - 1) % 2 ^ 256 = 2 ^ (101 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_101_hi :
    model_ln_wad_evm (2 ^ (101 + 1)) = 29254480743221599248233830204 := by
  have hlog : Nat.log2 (2 ^ (101 + 1)) = 102 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (101 + 1)) % 2 ^ 256 = 2 ^ (101 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_101_lo :
    model_ln_wad_to_wad_evm (2 ^ (101 + 1) - 1) = 29254480743221599248 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (101 + 1) - 1) % 2 ^ 256 = 2 ^ (101 + 1) - 1 by decide]
  rw [ray_eval_seam_101_lo]
  decide

private theorem wad_eval_seam_101_hi :
    model_ln_wad_to_wad_evm (2 ^ (101 + 1)) = 29254480743221599248 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (101 + 1)) % 2 ^ 256 = 2 ^ (101 + 1) by decide]
  rw [ray_eval_seam_101_hi]
  decide

private theorem ray_seam_101 :
    sle (model_ln_wad_evm (2 ^ (101 + 1) - 1)) (model_ln_wad_evm (2 ^ (101 + 1))) = true := by
  rw [ray_eval_seam_101_lo, ray_eval_seam_101_hi]
  unfold sle
  decide

private theorem wad_seam_101 :
    sle (model_ln_wad_to_wad_evm (2 ^ (101 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (101 + 1))) = true := by
  rw [wad_eval_seam_101_lo, wad_eval_seam_101_hi]
  unfold sle
  decide

private theorem ray_eval_seam_102_lo :
    model_ln_wad_evm (2 ^ (102 + 1) - 1) = 29947627923781544557651062325 := by
  have hlog : Nat.log2 (2 ^ (102 + 1) - 1) = 102 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (102 + 1) - 1) % 2 ^ 256 = 2 ^ (102 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_102_hi :
    model_ln_wad_evm (2 ^ (102 + 1)) = 29947627923781544557651062325 := by
  have hlog : Nat.log2 (2 ^ (102 + 1)) = 103 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (102 + 1)) % 2 ^ 256 = 2 ^ (102 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_102_lo :
    model_ln_wad_to_wad_evm (2 ^ (102 + 1) - 1) = 29947627923781544557 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (102 + 1) - 1) % 2 ^ 256 = 2 ^ (102 + 1) - 1 by decide]
  rw [ray_eval_seam_102_lo]
  decide

private theorem wad_eval_seam_102_hi :
    model_ln_wad_to_wad_evm (2 ^ (102 + 1)) = 29947627923781544557 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (102 + 1)) % 2 ^ 256 = 2 ^ (102 + 1) by decide]
  rw [ray_eval_seam_102_hi]
  decide

private theorem ray_seam_102 :
    sle (model_ln_wad_evm (2 ^ (102 + 1) - 1)) (model_ln_wad_evm (2 ^ (102 + 1))) = true := by
  rw [ray_eval_seam_102_lo, ray_eval_seam_102_hi]
  unfold sle
  decide

private theorem wad_seam_102 :
    sle (model_ln_wad_to_wad_evm (2 ^ (102 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (102 + 1))) = true := by
  rw [wad_eval_seam_102_lo, wad_eval_seam_102_hi]
  unfold sle
  decide

private theorem ray_eval_seam_103_lo :
    model_ln_wad_evm (2 ^ (103 + 1) - 1) = 30640775104341489867068294446 := by
  have hlog : Nat.log2 (2 ^ (103 + 1) - 1) = 103 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (103 + 1) - 1) % 2 ^ 256 = 2 ^ (103 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_103_hi :
    model_ln_wad_evm (2 ^ (103 + 1)) = 30640775104341489867068294447 := by
  have hlog : Nat.log2 (2 ^ (103 + 1)) = 104 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (103 + 1)) % 2 ^ 256 = 2 ^ (103 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_103_lo :
    model_ln_wad_to_wad_evm (2 ^ (103 + 1) - 1) = 30640775104341489867 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (103 + 1) - 1) % 2 ^ 256 = 2 ^ (103 + 1) - 1 by decide]
  rw [ray_eval_seam_103_lo]
  decide

private theorem wad_eval_seam_103_hi :
    model_ln_wad_to_wad_evm (2 ^ (103 + 1)) = 30640775104341489867 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (103 + 1)) % 2 ^ 256 = 2 ^ (103 + 1) by decide]
  rw [ray_eval_seam_103_hi]
  decide

private theorem ray_seam_103 :
    sle (model_ln_wad_evm (2 ^ (103 + 1) - 1)) (model_ln_wad_evm (2 ^ (103 + 1))) = true := by
  rw [ray_eval_seam_103_lo, ray_eval_seam_103_hi]
  unfold sle
  decide

private theorem wad_seam_103 :
    sle (model_ln_wad_to_wad_evm (2 ^ (103 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (103 + 1))) = true := by
  rw [wad_eval_seam_103_lo, wad_eval_seam_103_hi]
  unfold sle
  decide

private theorem ray_eval_seam_104_lo :
    model_ln_wad_evm (2 ^ (104 + 1) - 1) = 31333922284901435176485526568 := by
  have hlog : Nat.log2 (2 ^ (104 + 1) - 1) = 104 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (104 + 1) - 1) % 2 ^ 256 = 2 ^ (104 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_104_hi :
    model_ln_wad_evm (2 ^ (104 + 1)) = 31333922284901435176485526568 := by
  have hlog : Nat.log2 (2 ^ (104 + 1)) = 105 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (104 + 1)) % 2 ^ 256 = 2 ^ (104 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_104_lo :
    model_ln_wad_to_wad_evm (2 ^ (104 + 1) - 1) = 31333922284901435176 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (104 + 1) - 1) % 2 ^ 256 = 2 ^ (104 + 1) - 1 by decide]
  rw [ray_eval_seam_104_lo]
  decide

private theorem wad_eval_seam_104_hi :
    model_ln_wad_to_wad_evm (2 ^ (104 + 1)) = 31333922284901435176 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (104 + 1)) % 2 ^ 256 = 2 ^ (104 + 1) by decide]
  rw [ray_eval_seam_104_hi]
  decide

private theorem ray_seam_104 :
    sle (model_ln_wad_evm (2 ^ (104 + 1) - 1)) (model_ln_wad_evm (2 ^ (104 + 1))) = true := by
  rw [ray_eval_seam_104_lo, ray_eval_seam_104_hi]
  unfold sle
  decide

private theorem wad_seam_104 :
    sle (model_ln_wad_to_wad_evm (2 ^ (104 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (104 + 1))) = true := by
  rw [wad_eval_seam_104_lo, wad_eval_seam_104_hi]
  unfold sle
  decide

private theorem ray_eval_seam_105_lo :
    model_ln_wad_evm (2 ^ (105 + 1) - 1) = 32027069465461380485902758689 := by
  have hlog : Nat.log2 (2 ^ (105 + 1) - 1) = 105 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (105 + 1) - 1) % 2 ^ 256 = 2 ^ (105 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_105_hi :
    model_ln_wad_evm (2 ^ (105 + 1)) = 32027069465461380485902758690 := by
  have hlog : Nat.log2 (2 ^ (105 + 1)) = 106 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (105 + 1)) % 2 ^ 256 = 2 ^ (105 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_105_lo :
    model_ln_wad_to_wad_evm (2 ^ (105 + 1) - 1) = 32027069465461380485 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (105 + 1) - 1) % 2 ^ 256 = 2 ^ (105 + 1) - 1 by decide]
  rw [ray_eval_seam_105_lo]
  decide

private theorem wad_eval_seam_105_hi :
    model_ln_wad_to_wad_evm (2 ^ (105 + 1)) = 32027069465461380485 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (105 + 1)) % 2 ^ 256 = 2 ^ (105 + 1) by decide]
  rw [ray_eval_seam_105_hi]
  decide

private theorem ray_seam_105 :
    sle (model_ln_wad_evm (2 ^ (105 + 1) - 1)) (model_ln_wad_evm (2 ^ (105 + 1))) = true := by
  rw [ray_eval_seam_105_lo, ray_eval_seam_105_hi]
  unfold sle
  decide

private theorem wad_seam_105 :
    sle (model_ln_wad_to_wad_evm (2 ^ (105 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (105 + 1))) = true := by
  rw [wad_eval_seam_105_lo, wad_eval_seam_105_hi]
  unfold sle
  decide

private theorem ray_eval_seam_106_lo :
    model_ln_wad_evm (2 ^ (106 + 1) - 1) = 32720216646021325795319990811 := by
  have hlog : Nat.log2 (2 ^ (106 + 1) - 1) = 106 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (106 + 1) - 1) % 2 ^ 256 = 2 ^ (106 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_106_hi :
    model_ln_wad_evm (2 ^ (106 + 1)) = 32720216646021325795319990811 := by
  have hlog : Nat.log2 (2 ^ (106 + 1)) = 107 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (106 + 1)) % 2 ^ 256 = 2 ^ (106 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_106_lo :
    model_ln_wad_to_wad_evm (2 ^ (106 + 1) - 1) = 32720216646021325795 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (106 + 1) - 1) % 2 ^ 256 = 2 ^ (106 + 1) - 1 by decide]
  rw [ray_eval_seam_106_lo]
  decide

private theorem wad_eval_seam_106_hi :
    model_ln_wad_to_wad_evm (2 ^ (106 + 1)) = 32720216646021325795 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (106 + 1)) % 2 ^ 256 = 2 ^ (106 + 1) by decide]
  rw [ray_eval_seam_106_hi]
  decide

private theorem ray_seam_106 :
    sle (model_ln_wad_evm (2 ^ (106 + 1) - 1)) (model_ln_wad_evm (2 ^ (106 + 1))) = true := by
  rw [ray_eval_seam_106_lo, ray_eval_seam_106_hi]
  unfold sle
  decide

private theorem wad_seam_106 :
    sle (model_ln_wad_to_wad_evm (2 ^ (106 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (106 + 1))) = true := by
  rw [wad_eval_seam_106_lo, wad_eval_seam_106_hi]
  unfold sle
  decide

private theorem ray_eval_seam_107_lo :
    model_ln_wad_evm (2 ^ (107 + 1) - 1) = 33413363826581271104737222932 := by
  have hlog : Nat.log2 (2 ^ (107 + 1) - 1) = 107 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (107 + 1) - 1) % 2 ^ 256 = 2 ^ (107 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_107_hi :
    model_ln_wad_evm (2 ^ (107 + 1)) = 33413363826581271104737222933 := by
  have hlog : Nat.log2 (2 ^ (107 + 1)) = 108 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (107 + 1)) % 2 ^ 256 = 2 ^ (107 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_107_lo :
    model_ln_wad_to_wad_evm (2 ^ (107 + 1) - 1) = 33413363826581271104 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (107 + 1) - 1) % 2 ^ 256 = 2 ^ (107 + 1) - 1 by decide]
  rw [ray_eval_seam_107_lo]
  decide

private theorem wad_eval_seam_107_hi :
    model_ln_wad_to_wad_evm (2 ^ (107 + 1)) = 33413363826581271104 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (107 + 1)) % 2 ^ 256 = 2 ^ (107 + 1) by decide]
  rw [ray_eval_seam_107_hi]
  decide

private theorem ray_seam_107 :
    sle (model_ln_wad_evm (2 ^ (107 + 1) - 1)) (model_ln_wad_evm (2 ^ (107 + 1))) = true := by
  rw [ray_eval_seam_107_lo, ray_eval_seam_107_hi]
  unfold sle
  decide

private theorem wad_seam_107 :
    sle (model_ln_wad_to_wad_evm (2 ^ (107 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (107 + 1))) = true := by
  rw [wad_eval_seam_107_lo, wad_eval_seam_107_hi]
  unfold sle
  decide

private theorem ray_eval_seam_108_lo :
    model_ln_wad_evm (2 ^ (108 + 1) - 1) = 34106511007141216414154455053 := by
  have hlog : Nat.log2 (2 ^ (108 + 1) - 1) = 108 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (108 + 1) - 1) % 2 ^ 256 = 2 ^ (108 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_108_hi :
    model_ln_wad_evm (2 ^ (108 + 1)) = 34106511007141216414154455054 := by
  have hlog : Nat.log2 (2 ^ (108 + 1)) = 109 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (108 + 1)) % 2 ^ 256 = 2 ^ (108 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_108_lo :
    model_ln_wad_to_wad_evm (2 ^ (108 + 1) - 1) = 34106511007141216414 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (108 + 1) - 1) % 2 ^ 256 = 2 ^ (108 + 1) - 1 by decide]
  rw [ray_eval_seam_108_lo]
  decide

private theorem wad_eval_seam_108_hi :
    model_ln_wad_to_wad_evm (2 ^ (108 + 1)) = 34106511007141216414 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (108 + 1)) % 2 ^ 256 = 2 ^ (108 + 1) by decide]
  rw [ray_eval_seam_108_hi]
  decide

private theorem ray_seam_108 :
    sle (model_ln_wad_evm (2 ^ (108 + 1) - 1)) (model_ln_wad_evm (2 ^ (108 + 1))) = true := by
  rw [ray_eval_seam_108_lo, ray_eval_seam_108_hi]
  unfold sle
  decide

private theorem wad_seam_108 :
    sle (model_ln_wad_to_wad_evm (2 ^ (108 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (108 + 1))) = true := by
  rw [wad_eval_seam_108_lo, wad_eval_seam_108_hi]
  unfold sle
  decide

private theorem ray_eval_seam_109_lo :
    model_ln_wad_evm (2 ^ (109 + 1) - 1) = 34799658187701161723571687175 := by
  have hlog : Nat.log2 (2 ^ (109 + 1) - 1) = 109 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (109 + 1) - 1) % 2 ^ 256 = 2 ^ (109 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_109_hi :
    model_ln_wad_evm (2 ^ (109 + 1)) = 34799658187701161723571687176 := by
  have hlog : Nat.log2 (2 ^ (109 + 1)) = 110 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (109 + 1)) % 2 ^ 256 = 2 ^ (109 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_109_lo :
    model_ln_wad_to_wad_evm (2 ^ (109 + 1) - 1) = 34799658187701161723 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (109 + 1) - 1) % 2 ^ 256 = 2 ^ (109 + 1) - 1 by decide]
  rw [ray_eval_seam_109_lo]
  decide

private theorem wad_eval_seam_109_hi :
    model_ln_wad_to_wad_evm (2 ^ (109 + 1)) = 34799658187701161723 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (109 + 1)) % 2 ^ 256 = 2 ^ (109 + 1) by decide]
  rw [ray_eval_seam_109_hi]
  decide

private theorem ray_seam_109 :
    sle (model_ln_wad_evm (2 ^ (109 + 1) - 1)) (model_ln_wad_evm (2 ^ (109 + 1))) = true := by
  rw [ray_eval_seam_109_lo, ray_eval_seam_109_hi]
  unfold sle
  decide

private theorem wad_seam_109 :
    sle (model_ln_wad_to_wad_evm (2 ^ (109 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (109 + 1))) = true := by
  rw [wad_eval_seam_109_lo, wad_eval_seam_109_hi]
  unfold sle
  decide

private theorem ray_eval_seam_110_lo :
    model_ln_wad_evm (2 ^ (110 + 1) - 1) = 35492805368261107032988919296 := by
  have hlog : Nat.log2 (2 ^ (110 + 1) - 1) = 110 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (110 + 1) - 1) % 2 ^ 256 = 2 ^ (110 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_110_hi :
    model_ln_wad_evm (2 ^ (110 + 1)) = 35492805368261107032988919297 := by
  have hlog : Nat.log2 (2 ^ (110 + 1)) = 111 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (110 + 1)) % 2 ^ 256 = 2 ^ (110 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_110_lo :
    model_ln_wad_to_wad_evm (2 ^ (110 + 1) - 1) = 35492805368261107032 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (110 + 1) - 1) % 2 ^ 256 = 2 ^ (110 + 1) - 1 by decide]
  rw [ray_eval_seam_110_lo]
  decide

private theorem wad_eval_seam_110_hi :
    model_ln_wad_to_wad_evm (2 ^ (110 + 1)) = 35492805368261107032 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (110 + 1)) % 2 ^ 256 = 2 ^ (110 + 1) by decide]
  rw [ray_eval_seam_110_hi]
  decide

private theorem ray_seam_110 :
    sle (model_ln_wad_evm (2 ^ (110 + 1) - 1)) (model_ln_wad_evm (2 ^ (110 + 1))) = true := by
  rw [ray_eval_seam_110_lo, ray_eval_seam_110_hi]
  unfold sle
  decide

private theorem wad_seam_110 :
    sle (model_ln_wad_to_wad_evm (2 ^ (110 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (110 + 1))) = true := by
  rw [wad_eval_seam_110_lo, wad_eval_seam_110_hi]
  unfold sle
  decide

private theorem ray_eval_seam_111_lo :
    model_ln_wad_evm (2 ^ (111 + 1) - 1) = 36185952548821052342406151418 := by
  have hlog : Nat.log2 (2 ^ (111 + 1) - 1) = 111 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (111 + 1) - 1) % 2 ^ 256 = 2 ^ (111 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_111_hi :
    model_ln_wad_evm (2 ^ (111 + 1)) = 36185952548821052342406151418 := by
  have hlog : Nat.log2 (2 ^ (111 + 1)) = 112 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (111 + 1)) % 2 ^ 256 = 2 ^ (111 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_111_lo :
    model_ln_wad_to_wad_evm (2 ^ (111 + 1) - 1) = 36185952548821052342 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (111 + 1) - 1) % 2 ^ 256 = 2 ^ (111 + 1) - 1 by decide]
  rw [ray_eval_seam_111_lo]
  decide

private theorem wad_eval_seam_111_hi :
    model_ln_wad_to_wad_evm (2 ^ (111 + 1)) = 36185952548821052342 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (111 + 1)) % 2 ^ 256 = 2 ^ (111 + 1) by decide]
  rw [ray_eval_seam_111_hi]
  decide

private theorem ray_seam_111 :
    sle (model_ln_wad_evm (2 ^ (111 + 1) - 1)) (model_ln_wad_evm (2 ^ (111 + 1))) = true := by
  rw [ray_eval_seam_111_lo, ray_eval_seam_111_hi]
  unfold sle
  decide

private theorem wad_seam_111 :
    sle (model_ln_wad_to_wad_evm (2 ^ (111 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (111 + 1))) = true := by
  rw [wad_eval_seam_111_lo, wad_eval_seam_111_hi]
  unfold sle
  decide

private theorem ray_eval_seam_112_lo :
    model_ln_wad_evm (2 ^ (112 + 1) - 1) = 36879099729380997651823383539 := by
  have hlog : Nat.log2 (2 ^ (112 + 1) - 1) = 112 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (112 + 1) - 1) % 2 ^ 256 = 2 ^ (112 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_112_hi :
    model_ln_wad_evm (2 ^ (112 + 1)) = 36879099729380997651823383540 := by
  have hlog : Nat.log2 (2 ^ (112 + 1)) = 113 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (112 + 1)) % 2 ^ 256 = 2 ^ (112 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_112_lo :
    model_ln_wad_to_wad_evm (2 ^ (112 + 1) - 1) = 36879099729380997651 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (112 + 1) - 1) % 2 ^ 256 = 2 ^ (112 + 1) - 1 by decide]
  rw [ray_eval_seam_112_lo]
  decide

private theorem wad_eval_seam_112_hi :
    model_ln_wad_to_wad_evm (2 ^ (112 + 1)) = 36879099729380997651 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (112 + 1)) % 2 ^ 256 = 2 ^ (112 + 1) by decide]
  rw [ray_eval_seam_112_hi]
  decide

private theorem ray_seam_112 :
    sle (model_ln_wad_evm (2 ^ (112 + 1) - 1)) (model_ln_wad_evm (2 ^ (112 + 1))) = true := by
  rw [ray_eval_seam_112_lo, ray_eval_seam_112_hi]
  unfold sle
  decide

private theorem wad_seam_112 :
    sle (model_ln_wad_to_wad_evm (2 ^ (112 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (112 + 1))) = true := by
  rw [wad_eval_seam_112_lo, wad_eval_seam_112_hi]
  unfold sle
  decide

private theorem ray_eval_seam_113_lo :
    model_ln_wad_evm (2 ^ (113 + 1) - 1) = 37572246909940942961240615661 := by
  have hlog : Nat.log2 (2 ^ (113 + 1) - 1) = 113 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (113 + 1) - 1) % 2 ^ 256 = 2 ^ (113 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_113_hi :
    model_ln_wad_evm (2 ^ (113 + 1)) = 37572246909940942961240615661 := by
  have hlog : Nat.log2 (2 ^ (113 + 1)) = 114 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (113 + 1)) % 2 ^ 256 = 2 ^ (113 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_113_lo :
    model_ln_wad_to_wad_evm (2 ^ (113 + 1) - 1) = 37572246909940942961 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (113 + 1) - 1) % 2 ^ 256 = 2 ^ (113 + 1) - 1 by decide]
  rw [ray_eval_seam_113_lo]
  decide

private theorem wad_eval_seam_113_hi :
    model_ln_wad_to_wad_evm (2 ^ (113 + 1)) = 37572246909940942961 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (113 + 1)) % 2 ^ 256 = 2 ^ (113 + 1) by decide]
  rw [ray_eval_seam_113_hi]
  decide

private theorem ray_seam_113 :
    sle (model_ln_wad_evm (2 ^ (113 + 1) - 1)) (model_ln_wad_evm (2 ^ (113 + 1))) = true := by
  rw [ray_eval_seam_113_lo, ray_eval_seam_113_hi]
  unfold sle
  decide

private theorem wad_seam_113 :
    sle (model_ln_wad_to_wad_evm (2 ^ (113 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (113 + 1))) = true := by
  rw [wad_eval_seam_113_lo, wad_eval_seam_113_hi]
  unfold sle
  decide

private theorem ray_eval_seam_114_lo :
    model_ln_wad_evm (2 ^ (114 + 1) - 1) = 38265394090500888270657847782 := by
  have hlog : Nat.log2 (2 ^ (114 + 1) - 1) = 114 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (114 + 1) - 1) % 2 ^ 256 = 2 ^ (114 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_114_hi :
    model_ln_wad_evm (2 ^ (114 + 1)) = 38265394090500888270657847783 := by
  have hlog : Nat.log2 (2 ^ (114 + 1)) = 115 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (114 + 1)) % 2 ^ 256 = 2 ^ (114 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_114_lo :
    model_ln_wad_to_wad_evm (2 ^ (114 + 1) - 1) = 38265394090500888270 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (114 + 1) - 1) % 2 ^ 256 = 2 ^ (114 + 1) - 1 by decide]
  rw [ray_eval_seam_114_lo]
  decide

private theorem wad_eval_seam_114_hi :
    model_ln_wad_to_wad_evm (2 ^ (114 + 1)) = 38265394090500888270 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (114 + 1)) % 2 ^ 256 = 2 ^ (114 + 1) by decide]
  rw [ray_eval_seam_114_hi]
  decide

private theorem ray_seam_114 :
    sle (model_ln_wad_evm (2 ^ (114 + 1) - 1)) (model_ln_wad_evm (2 ^ (114 + 1))) = true := by
  rw [ray_eval_seam_114_lo, ray_eval_seam_114_hi]
  unfold sle
  decide

private theorem wad_seam_114 :
    sle (model_ln_wad_to_wad_evm (2 ^ (114 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (114 + 1))) = true := by
  rw [wad_eval_seam_114_lo, wad_eval_seam_114_hi]
  unfold sle
  decide

private theorem ray_eval_seam_115_lo :
    model_ln_wad_evm (2 ^ (115 + 1) - 1) = 38958541271060833580075079904 := by
  have hlog : Nat.log2 (2 ^ (115 + 1) - 1) = 115 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (115 + 1) - 1) % 2 ^ 256 = 2 ^ (115 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_115_hi :
    model_ln_wad_evm (2 ^ (115 + 1)) = 38958541271060833580075079904 := by
  have hlog : Nat.log2 (2 ^ (115 + 1)) = 116 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (115 + 1)) % 2 ^ 256 = 2 ^ (115 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_115_lo :
    model_ln_wad_to_wad_evm (2 ^ (115 + 1) - 1) = 38958541271060833580 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (115 + 1) - 1) % 2 ^ 256 = 2 ^ (115 + 1) - 1 by decide]
  rw [ray_eval_seam_115_lo]
  decide

private theorem wad_eval_seam_115_hi :
    model_ln_wad_to_wad_evm (2 ^ (115 + 1)) = 38958541271060833580 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (115 + 1)) % 2 ^ 256 = 2 ^ (115 + 1) by decide]
  rw [ray_eval_seam_115_hi]
  decide

private theorem ray_seam_115 :
    sle (model_ln_wad_evm (2 ^ (115 + 1) - 1)) (model_ln_wad_evm (2 ^ (115 + 1))) = true := by
  rw [ray_eval_seam_115_lo, ray_eval_seam_115_hi]
  unfold sle
  decide

private theorem wad_seam_115 :
    sle (model_ln_wad_to_wad_evm (2 ^ (115 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (115 + 1))) = true := by
  rw [wad_eval_seam_115_lo, wad_eval_seam_115_hi]
  unfold sle
  decide

private theorem ray_eval_seam_116_lo :
    model_ln_wad_evm (2 ^ (116 + 1) - 1) = 39651688451620778889492312025 := by
  have hlog : Nat.log2 (2 ^ (116 + 1) - 1) = 116 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (116 + 1) - 1) % 2 ^ 256 = 2 ^ (116 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_116_hi :
    model_ln_wad_evm (2 ^ (116 + 1)) = 39651688451620778889492312026 := by
  have hlog : Nat.log2 (2 ^ (116 + 1)) = 117 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (116 + 1)) % 2 ^ 256 = 2 ^ (116 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_116_lo :
    model_ln_wad_to_wad_evm (2 ^ (116 + 1) - 1) = 39651688451620778889 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (116 + 1) - 1) % 2 ^ 256 = 2 ^ (116 + 1) - 1 by decide]
  rw [ray_eval_seam_116_lo]
  decide

private theorem wad_eval_seam_116_hi :
    model_ln_wad_to_wad_evm (2 ^ (116 + 1)) = 39651688451620778889 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (116 + 1)) % 2 ^ 256 = 2 ^ (116 + 1) by decide]
  rw [ray_eval_seam_116_hi]
  decide

private theorem ray_seam_116 :
    sle (model_ln_wad_evm (2 ^ (116 + 1) - 1)) (model_ln_wad_evm (2 ^ (116 + 1))) = true := by
  rw [ray_eval_seam_116_lo, ray_eval_seam_116_hi]
  unfold sle
  decide

private theorem wad_seam_116 :
    sle (model_ln_wad_to_wad_evm (2 ^ (116 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (116 + 1))) = true := by
  rw [wad_eval_seam_116_lo, wad_eval_seam_116_hi]
  unfold sle
  decide

private theorem ray_eval_seam_117_lo :
    model_ln_wad_evm (2 ^ (117 + 1) - 1) = 40344835632180724198909544147 := by
  have hlog : Nat.log2 (2 ^ (117 + 1) - 1) = 117 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (117 + 1) - 1) % 2 ^ 256 = 2 ^ (117 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_117_hi :
    model_ln_wad_evm (2 ^ (117 + 1)) = 40344835632180724198909544147 := by
  have hlog : Nat.log2 (2 ^ (117 + 1)) = 118 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (117 + 1)) % 2 ^ 256 = 2 ^ (117 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_117_lo :
    model_ln_wad_to_wad_evm (2 ^ (117 + 1) - 1) = 40344835632180724198 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (117 + 1) - 1) % 2 ^ 256 = 2 ^ (117 + 1) - 1 by decide]
  rw [ray_eval_seam_117_lo]
  decide

private theorem wad_eval_seam_117_hi :
    model_ln_wad_to_wad_evm (2 ^ (117 + 1)) = 40344835632180724198 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (117 + 1)) % 2 ^ 256 = 2 ^ (117 + 1) by decide]
  rw [ray_eval_seam_117_hi]
  decide

private theorem ray_seam_117 :
    sle (model_ln_wad_evm (2 ^ (117 + 1) - 1)) (model_ln_wad_evm (2 ^ (117 + 1))) = true := by
  rw [ray_eval_seam_117_lo, ray_eval_seam_117_hi]
  unfold sle
  decide

private theorem wad_seam_117 :
    sle (model_ln_wad_to_wad_evm (2 ^ (117 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (117 + 1))) = true := by
  rw [wad_eval_seam_117_lo, wad_eval_seam_117_hi]
  unfold sle
  decide

private theorem ray_eval_seam_118_lo :
    model_ln_wad_evm (2 ^ (118 + 1) - 1) = 41037982812740669508326776268 := by
  have hlog : Nat.log2 (2 ^ (118 + 1) - 1) = 118 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (118 + 1) - 1) % 2 ^ 256 = 2 ^ (118 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_118_hi :
    model_ln_wad_evm (2 ^ (118 + 1)) = 41037982812740669508326776269 := by
  have hlog : Nat.log2 (2 ^ (118 + 1)) = 119 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (118 + 1)) % 2 ^ 256 = 2 ^ (118 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_118_lo :
    model_ln_wad_to_wad_evm (2 ^ (118 + 1) - 1) = 41037982812740669508 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (118 + 1) - 1) % 2 ^ 256 = 2 ^ (118 + 1) - 1 by decide]
  rw [ray_eval_seam_118_lo]
  decide

private theorem wad_eval_seam_118_hi :
    model_ln_wad_to_wad_evm (2 ^ (118 + 1)) = 41037982812740669508 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (118 + 1)) % 2 ^ 256 = 2 ^ (118 + 1) by decide]
  rw [ray_eval_seam_118_hi]
  decide

private theorem ray_seam_118 :
    sle (model_ln_wad_evm (2 ^ (118 + 1) - 1)) (model_ln_wad_evm (2 ^ (118 + 1))) = true := by
  rw [ray_eval_seam_118_lo, ray_eval_seam_118_hi]
  unfold sle
  decide

private theorem wad_seam_118 :
    sle (model_ln_wad_to_wad_evm (2 ^ (118 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (118 + 1))) = true := by
  rw [wad_eval_seam_118_lo, wad_eval_seam_118_hi]
  unfold sle
  decide

private theorem ray_eval_seam_119_lo :
    model_ln_wad_evm (2 ^ (119 + 1) - 1) = 41731129993300614817744008389 := by
  have hlog : Nat.log2 (2 ^ (119 + 1) - 1) = 119 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (119 + 1) - 1) % 2 ^ 256 = 2 ^ (119 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_119_hi :
    model_ln_wad_evm (2 ^ (119 + 1)) = 41731129993300614817744008390 := by
  have hlog : Nat.log2 (2 ^ (119 + 1)) = 120 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (119 + 1)) % 2 ^ 256 = 2 ^ (119 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_119_lo :
    model_ln_wad_to_wad_evm (2 ^ (119 + 1) - 1) = 41731129993300614817 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (119 + 1) - 1) % 2 ^ 256 = 2 ^ (119 + 1) - 1 by decide]
  rw [ray_eval_seam_119_lo]
  decide

private theorem wad_eval_seam_119_hi :
    model_ln_wad_to_wad_evm (2 ^ (119 + 1)) = 41731129993300614817 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (119 + 1)) % 2 ^ 256 = 2 ^ (119 + 1) by decide]
  rw [ray_eval_seam_119_hi]
  decide

private theorem ray_seam_119 :
    sle (model_ln_wad_evm (2 ^ (119 + 1) - 1)) (model_ln_wad_evm (2 ^ (119 + 1))) = true := by
  rw [ray_eval_seam_119_lo, ray_eval_seam_119_hi]
  unfold sle
  decide

private theorem wad_seam_119 :
    sle (model_ln_wad_to_wad_evm (2 ^ (119 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (119 + 1))) = true := by
  rw [wad_eval_seam_119_lo, wad_eval_seam_119_hi]
  unfold sle
  decide

private theorem ray_eval_seam_120_lo :
    model_ln_wad_evm (2 ^ (120 + 1) - 1) = 42424277173860560127161240511 := by
  have hlog : Nat.log2 (2 ^ (120 + 1) - 1) = 120 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (120 + 1) - 1) % 2 ^ 256 = 2 ^ (120 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_120_hi :
    model_ln_wad_evm (2 ^ (120 + 1)) = 42424277173860560127161240512 := by
  have hlog : Nat.log2 (2 ^ (120 + 1)) = 121 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (120 + 1)) % 2 ^ 256 = 2 ^ (120 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_120_lo :
    model_ln_wad_to_wad_evm (2 ^ (120 + 1) - 1) = 42424277173860560127 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (120 + 1) - 1) % 2 ^ 256 = 2 ^ (120 + 1) - 1 by decide]
  rw [ray_eval_seam_120_lo]
  decide

private theorem wad_eval_seam_120_hi :
    model_ln_wad_to_wad_evm (2 ^ (120 + 1)) = 42424277173860560127 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (120 + 1)) % 2 ^ 256 = 2 ^ (120 + 1) by decide]
  rw [ray_eval_seam_120_hi]
  decide

private theorem ray_seam_120 :
    sle (model_ln_wad_evm (2 ^ (120 + 1) - 1)) (model_ln_wad_evm (2 ^ (120 + 1))) = true := by
  rw [ray_eval_seam_120_lo, ray_eval_seam_120_hi]
  unfold sle
  decide

private theorem wad_seam_120 :
    sle (model_ln_wad_to_wad_evm (2 ^ (120 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (120 + 1))) = true := by
  rw [wad_eval_seam_120_lo, wad_eval_seam_120_hi]
  unfold sle
  decide

private theorem ray_eval_seam_121_lo :
    model_ln_wad_evm (2 ^ (121 + 1) - 1) = 43117424354420505436578472632 := by
  have hlog : Nat.log2 (2 ^ (121 + 1) - 1) = 121 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (121 + 1) - 1) % 2 ^ 256 = 2 ^ (121 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_121_hi :
    model_ln_wad_evm (2 ^ (121 + 1)) = 43117424354420505436578472633 := by
  have hlog : Nat.log2 (2 ^ (121 + 1)) = 122 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (121 + 1)) % 2 ^ 256 = 2 ^ (121 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_121_lo :
    model_ln_wad_to_wad_evm (2 ^ (121 + 1) - 1) = 43117424354420505436 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (121 + 1) - 1) % 2 ^ 256 = 2 ^ (121 + 1) - 1 by decide]
  rw [ray_eval_seam_121_lo]
  decide

private theorem wad_eval_seam_121_hi :
    model_ln_wad_to_wad_evm (2 ^ (121 + 1)) = 43117424354420505436 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (121 + 1)) % 2 ^ 256 = 2 ^ (121 + 1) by decide]
  rw [ray_eval_seam_121_hi]
  decide

private theorem ray_seam_121 :
    sle (model_ln_wad_evm (2 ^ (121 + 1) - 1)) (model_ln_wad_evm (2 ^ (121 + 1))) = true := by
  rw [ray_eval_seam_121_lo, ray_eval_seam_121_hi]
  unfold sle
  decide

private theorem wad_seam_121 :
    sle (model_ln_wad_to_wad_evm (2 ^ (121 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (121 + 1))) = true := by
  rw [wad_eval_seam_121_lo, wad_eval_seam_121_hi]
  unfold sle
  decide

private theorem ray_eval_seam_122_lo :
    model_ln_wad_evm (2 ^ (122 + 1) - 1) = 43810571534980450745995704754 := by
  have hlog : Nat.log2 (2 ^ (122 + 1) - 1) = 122 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (122 + 1) - 1) % 2 ^ 256 = 2 ^ (122 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_122_hi :
    model_ln_wad_evm (2 ^ (122 + 1)) = 43810571534980450745995704755 := by
  have hlog : Nat.log2 (2 ^ (122 + 1)) = 123 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (122 + 1)) % 2 ^ 256 = 2 ^ (122 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_122_lo :
    model_ln_wad_to_wad_evm (2 ^ (122 + 1) - 1) = 43810571534980450745 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (122 + 1) - 1) % 2 ^ 256 = 2 ^ (122 + 1) - 1 by decide]
  rw [ray_eval_seam_122_lo]
  decide

private theorem wad_eval_seam_122_hi :
    model_ln_wad_to_wad_evm (2 ^ (122 + 1)) = 43810571534980450745 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (122 + 1)) % 2 ^ 256 = 2 ^ (122 + 1) by decide]
  rw [ray_eval_seam_122_hi]
  decide

private theorem ray_seam_122 :
    sle (model_ln_wad_evm (2 ^ (122 + 1) - 1)) (model_ln_wad_evm (2 ^ (122 + 1))) = true := by
  rw [ray_eval_seam_122_lo, ray_eval_seam_122_hi]
  unfold sle
  decide

private theorem wad_seam_122 :
    sle (model_ln_wad_to_wad_evm (2 ^ (122 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (122 + 1))) = true := by
  rw [wad_eval_seam_122_lo, wad_eval_seam_122_hi]
  unfold sle
  decide

private theorem ray_eval_seam_123_lo :
    model_ln_wad_evm (2 ^ (123 + 1) - 1) = 44503718715540396055412936875 := by
  have hlog : Nat.log2 (2 ^ (123 + 1) - 1) = 123 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (123 + 1) - 1) % 2 ^ 256 = 2 ^ (123 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_123_hi :
    model_ln_wad_evm (2 ^ (123 + 1)) = 44503718715540396055412936876 := by
  have hlog : Nat.log2 (2 ^ (123 + 1)) = 124 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (123 + 1)) % 2 ^ 256 = 2 ^ (123 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_123_lo :
    model_ln_wad_to_wad_evm (2 ^ (123 + 1) - 1) = 44503718715540396055 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (123 + 1) - 1) % 2 ^ 256 = 2 ^ (123 + 1) - 1 by decide]
  rw [ray_eval_seam_123_lo]
  decide

private theorem wad_eval_seam_123_hi :
    model_ln_wad_to_wad_evm (2 ^ (123 + 1)) = 44503718715540396055 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (123 + 1)) % 2 ^ 256 = 2 ^ (123 + 1) by decide]
  rw [ray_eval_seam_123_hi]
  decide

private theorem ray_seam_123 :
    sle (model_ln_wad_evm (2 ^ (123 + 1) - 1)) (model_ln_wad_evm (2 ^ (123 + 1))) = true := by
  rw [ray_eval_seam_123_lo, ray_eval_seam_123_hi]
  unfold sle
  decide

private theorem wad_seam_123 :
    sle (model_ln_wad_to_wad_evm (2 ^ (123 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (123 + 1))) = true := by
  rw [wad_eval_seam_123_lo, wad_eval_seam_123_hi]
  unfold sle
  decide

private theorem ray_eval_seam_124_lo :
    model_ln_wad_evm (2 ^ (124 + 1) - 1) = 45196865896100341364830168997 := by
  have hlog : Nat.log2 (2 ^ (124 + 1) - 1) = 124 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (124 + 1) - 1) % 2 ^ 256 = 2 ^ (124 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_124_hi :
    model_ln_wad_evm (2 ^ (124 + 1)) = 45196865896100341364830168997 := by
  have hlog : Nat.log2 (2 ^ (124 + 1)) = 125 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (124 + 1)) % 2 ^ 256 = 2 ^ (124 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_124_lo :
    model_ln_wad_to_wad_evm (2 ^ (124 + 1) - 1) = 45196865896100341364 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (124 + 1) - 1) % 2 ^ 256 = 2 ^ (124 + 1) - 1 by decide]
  rw [ray_eval_seam_124_lo]
  decide

private theorem wad_eval_seam_124_hi :
    model_ln_wad_to_wad_evm (2 ^ (124 + 1)) = 45196865896100341364 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (124 + 1)) % 2 ^ 256 = 2 ^ (124 + 1) by decide]
  rw [ray_eval_seam_124_hi]
  decide

private theorem ray_seam_124 :
    sle (model_ln_wad_evm (2 ^ (124 + 1) - 1)) (model_ln_wad_evm (2 ^ (124 + 1))) = true := by
  rw [ray_eval_seam_124_lo, ray_eval_seam_124_hi]
  unfold sle
  decide

private theorem wad_seam_124 :
    sle (model_ln_wad_to_wad_evm (2 ^ (124 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (124 + 1))) = true := by
  rw [wad_eval_seam_124_lo, wad_eval_seam_124_hi]
  unfold sle
  decide

private theorem ray_eval_seam_125_lo :
    model_ln_wad_evm (2 ^ (125 + 1) - 1) = 45890013076660286674247401118 := by
  have hlog : Nat.log2 (2 ^ (125 + 1) - 1) = 125 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (125 + 1) - 1) % 2 ^ 256 = 2 ^ (125 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_125_hi :
    model_ln_wad_evm (2 ^ (125 + 1)) = 45890013076660286674247401119 := by
  have hlog : Nat.log2 (2 ^ (125 + 1)) = 126 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (125 + 1)) % 2 ^ 256 = 2 ^ (125 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_125_lo :
    model_ln_wad_to_wad_evm (2 ^ (125 + 1) - 1) = 45890013076660286674 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (125 + 1) - 1) % 2 ^ 256 = 2 ^ (125 + 1) - 1 by decide]
  rw [ray_eval_seam_125_lo]
  decide

private theorem wad_eval_seam_125_hi :
    model_ln_wad_to_wad_evm (2 ^ (125 + 1)) = 45890013076660286674 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (125 + 1)) % 2 ^ 256 = 2 ^ (125 + 1) by decide]
  rw [ray_eval_seam_125_hi]
  decide

private theorem ray_seam_125 :
    sle (model_ln_wad_evm (2 ^ (125 + 1) - 1)) (model_ln_wad_evm (2 ^ (125 + 1))) = true := by
  rw [ray_eval_seam_125_lo, ray_eval_seam_125_hi]
  unfold sle
  decide

private theorem wad_seam_125 :
    sle (model_ln_wad_to_wad_evm (2 ^ (125 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (125 + 1))) = true := by
  rw [wad_eval_seam_125_lo, wad_eval_seam_125_hi]
  unfold sle
  decide

private theorem ray_eval_seam_126_lo :
    model_ln_wad_evm (2 ^ (126 + 1) - 1) = 46583160257220231983664633240 := by
  have hlog : Nat.log2 (2 ^ (126 + 1) - 1) = 126 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (126 + 1) - 1) % 2 ^ 256 = 2 ^ (126 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_126_hi :
    model_ln_wad_evm (2 ^ (126 + 1)) = 46583160257220231983664633240 := by
  have hlog : Nat.log2 (2 ^ (126 + 1)) = 127 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (126 + 1)) % 2 ^ 256 = 2 ^ (126 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_126_lo :
    model_ln_wad_to_wad_evm (2 ^ (126 + 1) - 1) = 46583160257220231983 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (126 + 1) - 1) % 2 ^ 256 = 2 ^ (126 + 1) - 1 by decide]
  rw [ray_eval_seam_126_lo]
  decide

private theorem wad_eval_seam_126_hi :
    model_ln_wad_to_wad_evm (2 ^ (126 + 1)) = 46583160257220231983 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (126 + 1)) % 2 ^ 256 = 2 ^ (126 + 1) by decide]
  rw [ray_eval_seam_126_hi]
  decide

private theorem ray_seam_126 :
    sle (model_ln_wad_evm (2 ^ (126 + 1) - 1)) (model_ln_wad_evm (2 ^ (126 + 1))) = true := by
  rw [ray_eval_seam_126_lo, ray_eval_seam_126_hi]
  unfold sle
  decide

private theorem wad_seam_126 :
    sle (model_ln_wad_to_wad_evm (2 ^ (126 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (126 + 1))) = true := by
  rw [wad_eval_seam_126_lo, wad_eval_seam_126_hi]
  unfold sle
  decide

private theorem ray_eval_seam_127_lo :
    model_ln_wad_evm (2 ^ (127 + 1) - 1) = 47276307437780177293081865361 := by
  have hlog : Nat.log2 (2 ^ (127 + 1) - 1) = 127 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (127 + 1) - 1) % 2 ^ 256 = 2 ^ (127 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_127_hi :
    model_ln_wad_evm (2 ^ (127 + 1)) = 47276307437780177293081865362 := by
  have hlog : Nat.log2 (2 ^ (127 + 1)) = 128 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (127 + 1)) % 2 ^ 256 = 2 ^ (127 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_127_lo :
    model_ln_wad_to_wad_evm (2 ^ (127 + 1) - 1) = 47276307437780177293 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (127 + 1) - 1) % 2 ^ 256 = 2 ^ (127 + 1) - 1 by decide]
  rw [ray_eval_seam_127_lo]
  decide

private theorem wad_eval_seam_127_hi :
    model_ln_wad_to_wad_evm (2 ^ (127 + 1)) = 47276307437780177293 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (127 + 1)) % 2 ^ 256 = 2 ^ (127 + 1) by decide]
  rw [ray_eval_seam_127_hi]
  decide

private theorem ray_seam_127 :
    sle (model_ln_wad_evm (2 ^ (127 + 1) - 1)) (model_ln_wad_evm (2 ^ (127 + 1))) = true := by
  rw [ray_eval_seam_127_lo, ray_eval_seam_127_hi]
  unfold sle
  decide

private theorem wad_seam_127 :
    sle (model_ln_wad_to_wad_evm (2 ^ (127 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (127 + 1))) = true := by
  rw [wad_eval_seam_127_lo, wad_eval_seam_127_hi]
  unfold sle
  decide

private theorem ray_eval_seam_128_lo :
    model_ln_wad_evm (2 ^ (128 + 1) - 1) = 47969454618340122602499097483 := by
  have hlog : Nat.log2 (2 ^ (128 + 1) - 1) = 128 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (128 + 1) - 1) % 2 ^ 256 = 2 ^ (128 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_128_hi :
    model_ln_wad_evm (2 ^ (128 + 1)) = 47969454618340122602499097483 := by
  have hlog : Nat.log2 (2 ^ (128 + 1)) = 129 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (128 + 1)) % 2 ^ 256 = 2 ^ (128 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_128_lo :
    model_ln_wad_to_wad_evm (2 ^ (128 + 1) - 1) = 47969454618340122602 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (128 + 1) - 1) % 2 ^ 256 = 2 ^ (128 + 1) - 1 by decide]
  rw [ray_eval_seam_128_lo]
  decide

private theorem wad_eval_seam_128_hi :
    model_ln_wad_to_wad_evm (2 ^ (128 + 1)) = 47969454618340122602 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (128 + 1)) % 2 ^ 256 = 2 ^ (128 + 1) by decide]
  rw [ray_eval_seam_128_hi]
  decide

private theorem ray_seam_128 :
    sle (model_ln_wad_evm (2 ^ (128 + 1) - 1)) (model_ln_wad_evm (2 ^ (128 + 1))) = true := by
  rw [ray_eval_seam_128_lo, ray_eval_seam_128_hi]
  unfold sle
  decide

private theorem wad_seam_128 :
    sle (model_ln_wad_to_wad_evm (2 ^ (128 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (128 + 1))) = true := by
  rw [wad_eval_seam_128_lo, wad_eval_seam_128_hi]
  unfold sle
  decide

private theorem ray_eval_seam_129_lo :
    model_ln_wad_evm (2 ^ (129 + 1) - 1) = 48662601798900067911916329604 := by
  have hlog : Nat.log2 (2 ^ (129 + 1) - 1) = 129 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (129 + 1) - 1) % 2 ^ 256 = 2 ^ (129 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_129_hi :
    model_ln_wad_evm (2 ^ (129 + 1)) = 48662601798900067911916329605 := by
  have hlog : Nat.log2 (2 ^ (129 + 1)) = 130 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (129 + 1)) % 2 ^ 256 = 2 ^ (129 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_129_lo :
    model_ln_wad_to_wad_evm (2 ^ (129 + 1) - 1) = 48662601798900067911 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (129 + 1) - 1) % 2 ^ 256 = 2 ^ (129 + 1) - 1 by decide]
  rw [ray_eval_seam_129_lo]
  decide

private theorem wad_eval_seam_129_hi :
    model_ln_wad_to_wad_evm (2 ^ (129 + 1)) = 48662601798900067911 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (129 + 1)) % 2 ^ 256 = 2 ^ (129 + 1) by decide]
  rw [ray_eval_seam_129_hi]
  decide

private theorem ray_seam_129 :
    sle (model_ln_wad_evm (2 ^ (129 + 1) - 1)) (model_ln_wad_evm (2 ^ (129 + 1))) = true := by
  rw [ray_eval_seam_129_lo, ray_eval_seam_129_hi]
  unfold sle
  decide

private theorem wad_seam_129 :
    sle (model_ln_wad_to_wad_evm (2 ^ (129 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (129 + 1))) = true := by
  rw [wad_eval_seam_129_lo, wad_eval_seam_129_hi]
  unfold sle
  decide

private theorem ray_eval_seam_130_lo :
    model_ln_wad_evm (2 ^ (130 + 1) - 1) = 49355748979460013221333561726 := by
  have hlog : Nat.log2 (2 ^ (130 + 1) - 1) = 130 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (130 + 1) - 1) % 2 ^ 256 = 2 ^ (130 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_130_hi :
    model_ln_wad_evm (2 ^ (130 + 1)) = 49355748979460013221333561726 := by
  have hlog : Nat.log2 (2 ^ (130 + 1)) = 131 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (130 + 1)) % 2 ^ 256 = 2 ^ (130 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_130_lo :
    model_ln_wad_to_wad_evm (2 ^ (130 + 1) - 1) = 49355748979460013221 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (130 + 1) - 1) % 2 ^ 256 = 2 ^ (130 + 1) - 1 by decide]
  rw [ray_eval_seam_130_lo]
  decide

private theorem wad_eval_seam_130_hi :
    model_ln_wad_to_wad_evm (2 ^ (130 + 1)) = 49355748979460013221 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (130 + 1)) % 2 ^ 256 = 2 ^ (130 + 1) by decide]
  rw [ray_eval_seam_130_hi]
  decide

private theorem ray_seam_130 :
    sle (model_ln_wad_evm (2 ^ (130 + 1) - 1)) (model_ln_wad_evm (2 ^ (130 + 1))) = true := by
  rw [ray_eval_seam_130_lo, ray_eval_seam_130_hi]
  unfold sle
  decide

private theorem wad_seam_130 :
    sle (model_ln_wad_to_wad_evm (2 ^ (130 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (130 + 1))) = true := by
  rw [wad_eval_seam_130_lo, wad_eval_seam_130_hi]
  unfold sle
  decide

private theorem ray_eval_seam_131_lo :
    model_ln_wad_evm (2 ^ (131 + 1) - 1) = 50048896160019958530750793847 := by
  have hlog : Nat.log2 (2 ^ (131 + 1) - 1) = 131 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (131 + 1) - 1) % 2 ^ 256 = 2 ^ (131 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_131_hi :
    model_ln_wad_evm (2 ^ (131 + 1)) = 50048896160019958530750793848 := by
  have hlog : Nat.log2 (2 ^ (131 + 1)) = 132 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (131 + 1)) % 2 ^ 256 = 2 ^ (131 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_131_lo :
    model_ln_wad_to_wad_evm (2 ^ (131 + 1) - 1) = 50048896160019958530 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (131 + 1) - 1) % 2 ^ 256 = 2 ^ (131 + 1) - 1 by decide]
  rw [ray_eval_seam_131_lo]
  decide

private theorem wad_eval_seam_131_hi :
    model_ln_wad_to_wad_evm (2 ^ (131 + 1)) = 50048896160019958530 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (131 + 1)) % 2 ^ 256 = 2 ^ (131 + 1) by decide]
  rw [ray_eval_seam_131_hi]
  decide

private theorem ray_seam_131 :
    sle (model_ln_wad_evm (2 ^ (131 + 1) - 1)) (model_ln_wad_evm (2 ^ (131 + 1))) = true := by
  rw [ray_eval_seam_131_lo, ray_eval_seam_131_hi]
  unfold sle
  decide

private theorem wad_seam_131 :
    sle (model_ln_wad_to_wad_evm (2 ^ (131 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (131 + 1))) = true := by
  rw [wad_eval_seam_131_lo, wad_eval_seam_131_hi]
  unfold sle
  decide

private theorem ray_eval_seam_132_lo :
    model_ln_wad_evm (2 ^ (132 + 1) - 1) = 50742043340579903840168025968 := by
  have hlog : Nat.log2 (2 ^ (132 + 1) - 1) = 132 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (132 + 1) - 1) % 2 ^ 256 = 2 ^ (132 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_132_hi :
    model_ln_wad_evm (2 ^ (132 + 1)) = 50742043340579903840168025969 := by
  have hlog : Nat.log2 (2 ^ (132 + 1)) = 133 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (132 + 1)) % 2 ^ 256 = 2 ^ (132 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_132_lo :
    model_ln_wad_to_wad_evm (2 ^ (132 + 1) - 1) = 50742043340579903840 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (132 + 1) - 1) % 2 ^ 256 = 2 ^ (132 + 1) - 1 by decide]
  rw [ray_eval_seam_132_lo]
  decide

private theorem wad_eval_seam_132_hi :
    model_ln_wad_to_wad_evm (2 ^ (132 + 1)) = 50742043340579903840 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (132 + 1)) % 2 ^ 256 = 2 ^ (132 + 1) by decide]
  rw [ray_eval_seam_132_hi]
  decide

private theorem ray_seam_132 :
    sle (model_ln_wad_evm (2 ^ (132 + 1) - 1)) (model_ln_wad_evm (2 ^ (132 + 1))) = true := by
  rw [ray_eval_seam_132_lo, ray_eval_seam_132_hi]
  unfold sle
  decide

private theorem wad_seam_132 :
    sle (model_ln_wad_to_wad_evm (2 ^ (132 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (132 + 1))) = true := by
  rw [wad_eval_seam_132_lo, wad_eval_seam_132_hi]
  unfold sle
  decide

private theorem ray_eval_seam_133_lo :
    model_ln_wad_evm (2 ^ (133 + 1) - 1) = 51435190521139849149585258090 := by
  have hlog : Nat.log2 (2 ^ (133 + 1) - 1) = 133 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (133 + 1) - 1) % 2 ^ 256 = 2 ^ (133 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_133_hi :
    model_ln_wad_evm (2 ^ (133 + 1)) = 51435190521139849149585258091 := by
  have hlog : Nat.log2 (2 ^ (133 + 1)) = 134 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (133 + 1)) % 2 ^ 256 = 2 ^ (133 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_133_lo :
    model_ln_wad_to_wad_evm (2 ^ (133 + 1) - 1) = 51435190521139849149 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (133 + 1) - 1) % 2 ^ 256 = 2 ^ (133 + 1) - 1 by decide]
  rw [ray_eval_seam_133_lo]
  decide

private theorem wad_eval_seam_133_hi :
    model_ln_wad_to_wad_evm (2 ^ (133 + 1)) = 51435190521139849149 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (133 + 1)) % 2 ^ 256 = 2 ^ (133 + 1) by decide]
  rw [ray_eval_seam_133_hi]
  decide

private theorem ray_seam_133 :
    sle (model_ln_wad_evm (2 ^ (133 + 1) - 1)) (model_ln_wad_evm (2 ^ (133 + 1))) = true := by
  rw [ray_eval_seam_133_lo, ray_eval_seam_133_hi]
  unfold sle
  decide

private theorem wad_seam_133 :
    sle (model_ln_wad_to_wad_evm (2 ^ (133 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (133 + 1))) = true := by
  rw [wad_eval_seam_133_lo, wad_eval_seam_133_hi]
  unfold sle
  decide

private theorem ray_eval_seam_134_lo :
    model_ln_wad_evm (2 ^ (134 + 1) - 1) = 52128337701699794459002490211 := by
  have hlog : Nat.log2 (2 ^ (134 + 1) - 1) = 134 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (134 + 1) - 1) % 2 ^ 256 = 2 ^ (134 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_134_hi :
    model_ln_wad_evm (2 ^ (134 + 1)) = 52128337701699794459002490212 := by
  have hlog : Nat.log2 (2 ^ (134 + 1)) = 135 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (134 + 1)) % 2 ^ 256 = 2 ^ (134 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_134_lo :
    model_ln_wad_to_wad_evm (2 ^ (134 + 1) - 1) = 52128337701699794459 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (134 + 1) - 1) % 2 ^ 256 = 2 ^ (134 + 1) - 1 by decide]
  rw [ray_eval_seam_134_lo]
  decide

private theorem wad_eval_seam_134_hi :
    model_ln_wad_to_wad_evm (2 ^ (134 + 1)) = 52128337701699794459 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (134 + 1)) % 2 ^ 256 = 2 ^ (134 + 1) by decide]
  rw [ray_eval_seam_134_hi]
  decide

private theorem ray_seam_134 :
    sle (model_ln_wad_evm (2 ^ (134 + 1) - 1)) (model_ln_wad_evm (2 ^ (134 + 1))) = true := by
  rw [ray_eval_seam_134_lo, ray_eval_seam_134_hi]
  unfold sle
  decide

private theorem wad_seam_134 :
    sle (model_ln_wad_to_wad_evm (2 ^ (134 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (134 + 1))) = true := by
  rw [wad_eval_seam_134_lo, wad_eval_seam_134_hi]
  unfold sle
  decide

private theorem ray_eval_seam_135_lo :
    model_ln_wad_evm (2 ^ (135 + 1) - 1) = 52821484882259739768419722333 := by
  have hlog : Nat.log2 (2 ^ (135 + 1) - 1) = 135 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (135 + 1) - 1) % 2 ^ 256 = 2 ^ (135 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_135_hi :
    model_ln_wad_evm (2 ^ (135 + 1)) = 52821484882259739768419722333 := by
  have hlog : Nat.log2 (2 ^ (135 + 1)) = 136 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (135 + 1)) % 2 ^ 256 = 2 ^ (135 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_135_lo :
    model_ln_wad_to_wad_evm (2 ^ (135 + 1) - 1) = 52821484882259739768 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (135 + 1) - 1) % 2 ^ 256 = 2 ^ (135 + 1) - 1 by decide]
  rw [ray_eval_seam_135_lo]
  decide

private theorem wad_eval_seam_135_hi :
    model_ln_wad_to_wad_evm (2 ^ (135 + 1)) = 52821484882259739768 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (135 + 1)) % 2 ^ 256 = 2 ^ (135 + 1) by decide]
  rw [ray_eval_seam_135_hi]
  decide

private theorem ray_seam_135 :
    sle (model_ln_wad_evm (2 ^ (135 + 1) - 1)) (model_ln_wad_evm (2 ^ (135 + 1))) = true := by
  rw [ray_eval_seam_135_lo, ray_eval_seam_135_hi]
  unfold sle
  decide

private theorem wad_seam_135 :
    sle (model_ln_wad_to_wad_evm (2 ^ (135 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (135 + 1))) = true := by
  rw [wad_eval_seam_135_lo, wad_eval_seam_135_hi]
  unfold sle
  decide

private theorem ray_eval_seam_136_lo :
    model_ln_wad_evm (2 ^ (136 + 1) - 1) = 53514632062819685077836954454 := by
  have hlog : Nat.log2 (2 ^ (136 + 1) - 1) = 136 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (136 + 1) - 1) % 2 ^ 256 = 2 ^ (136 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_136_hi :
    model_ln_wad_evm (2 ^ (136 + 1)) = 53514632062819685077836954455 := by
  have hlog : Nat.log2 (2 ^ (136 + 1)) = 137 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (136 + 1)) % 2 ^ 256 = 2 ^ (136 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_136_lo :
    model_ln_wad_to_wad_evm (2 ^ (136 + 1) - 1) = 53514632062819685077 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (136 + 1) - 1) % 2 ^ 256 = 2 ^ (136 + 1) - 1 by decide]
  rw [ray_eval_seam_136_lo]
  decide

private theorem wad_eval_seam_136_hi :
    model_ln_wad_to_wad_evm (2 ^ (136 + 1)) = 53514632062819685077 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (136 + 1)) % 2 ^ 256 = 2 ^ (136 + 1) by decide]
  rw [ray_eval_seam_136_hi]
  decide

private theorem ray_seam_136 :
    sle (model_ln_wad_evm (2 ^ (136 + 1) - 1)) (model_ln_wad_evm (2 ^ (136 + 1))) = true := by
  rw [ray_eval_seam_136_lo, ray_eval_seam_136_hi]
  unfold sle
  decide

private theorem wad_seam_136 :
    sle (model_ln_wad_to_wad_evm (2 ^ (136 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (136 + 1))) = true := by
  rw [wad_eval_seam_136_lo, wad_eval_seam_136_hi]
  unfold sle
  decide

private theorem ray_eval_seam_137_lo :
    model_ln_wad_evm (2 ^ (137 + 1) - 1) = 54207779243379630387254186576 := by
  have hlog : Nat.log2 (2 ^ (137 + 1) - 1) = 137 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (137 + 1) - 1) % 2 ^ 256 = 2 ^ (137 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_137_hi :
    model_ln_wad_evm (2 ^ (137 + 1)) = 54207779243379630387254186576 := by
  have hlog : Nat.log2 (2 ^ (137 + 1)) = 138 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (137 + 1)) % 2 ^ 256 = 2 ^ (137 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_137_lo :
    model_ln_wad_to_wad_evm (2 ^ (137 + 1) - 1) = 54207779243379630387 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (137 + 1) - 1) % 2 ^ 256 = 2 ^ (137 + 1) - 1 by decide]
  rw [ray_eval_seam_137_lo]
  decide

private theorem wad_eval_seam_137_hi :
    model_ln_wad_to_wad_evm (2 ^ (137 + 1)) = 54207779243379630387 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (137 + 1)) % 2 ^ 256 = 2 ^ (137 + 1) by decide]
  rw [ray_eval_seam_137_hi]
  decide

private theorem ray_seam_137 :
    sle (model_ln_wad_evm (2 ^ (137 + 1) - 1)) (model_ln_wad_evm (2 ^ (137 + 1))) = true := by
  rw [ray_eval_seam_137_lo, ray_eval_seam_137_hi]
  unfold sle
  decide

private theorem wad_seam_137 :
    sle (model_ln_wad_to_wad_evm (2 ^ (137 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (137 + 1))) = true := by
  rw [wad_eval_seam_137_lo, wad_eval_seam_137_hi]
  unfold sle
  decide

private theorem ray_eval_seam_138_lo :
    model_ln_wad_evm (2 ^ (138 + 1) - 1) = 54900926423939575696671418697 := by
  have hlog : Nat.log2 (2 ^ (138 + 1) - 1) = 138 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (138 + 1) - 1) % 2 ^ 256 = 2 ^ (138 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_138_hi :
    model_ln_wad_evm (2 ^ (138 + 1)) = 54900926423939575696671418698 := by
  have hlog : Nat.log2 (2 ^ (138 + 1)) = 139 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (138 + 1)) % 2 ^ 256 = 2 ^ (138 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_138_lo :
    model_ln_wad_to_wad_evm (2 ^ (138 + 1) - 1) = 54900926423939575696 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (138 + 1) - 1) % 2 ^ 256 = 2 ^ (138 + 1) - 1 by decide]
  rw [ray_eval_seam_138_lo]
  decide

private theorem wad_eval_seam_138_hi :
    model_ln_wad_to_wad_evm (2 ^ (138 + 1)) = 54900926423939575696 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (138 + 1)) % 2 ^ 256 = 2 ^ (138 + 1) by decide]
  rw [ray_eval_seam_138_hi]
  decide

private theorem ray_seam_138 :
    sle (model_ln_wad_evm (2 ^ (138 + 1) - 1)) (model_ln_wad_evm (2 ^ (138 + 1))) = true := by
  rw [ray_eval_seam_138_lo, ray_eval_seam_138_hi]
  unfold sle
  decide

private theorem wad_seam_138 :
    sle (model_ln_wad_to_wad_evm (2 ^ (138 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (138 + 1))) = true := by
  rw [wad_eval_seam_138_lo, wad_eval_seam_138_hi]
  unfold sle
  decide

private theorem ray_eval_seam_139_lo :
    model_ln_wad_evm (2 ^ (139 + 1) - 1) = 55594073604499521006088650819 := by
  have hlog : Nat.log2 (2 ^ (139 + 1) - 1) = 139 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (139 + 1) - 1) % 2 ^ 256 = 2 ^ (139 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_139_hi :
    model_ln_wad_evm (2 ^ (139 + 1)) = 55594073604499521006088650819 := by
  have hlog : Nat.log2 (2 ^ (139 + 1)) = 140 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (139 + 1)) % 2 ^ 256 = 2 ^ (139 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_139_lo :
    model_ln_wad_to_wad_evm (2 ^ (139 + 1) - 1) = 55594073604499521006 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (139 + 1) - 1) % 2 ^ 256 = 2 ^ (139 + 1) - 1 by decide]
  rw [ray_eval_seam_139_lo]
  decide

private theorem wad_eval_seam_139_hi :
    model_ln_wad_to_wad_evm (2 ^ (139 + 1)) = 55594073604499521006 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (139 + 1)) % 2 ^ 256 = 2 ^ (139 + 1) by decide]
  rw [ray_eval_seam_139_hi]
  decide

private theorem ray_seam_139 :
    sle (model_ln_wad_evm (2 ^ (139 + 1) - 1)) (model_ln_wad_evm (2 ^ (139 + 1))) = true := by
  rw [ray_eval_seam_139_lo, ray_eval_seam_139_hi]
  unfold sle
  decide

private theorem wad_seam_139 :
    sle (model_ln_wad_to_wad_evm (2 ^ (139 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (139 + 1))) = true := by
  rw [wad_eval_seam_139_lo, wad_eval_seam_139_hi]
  unfold sle
  decide

private theorem ray_eval_seam_140_lo :
    model_ln_wad_evm (2 ^ (140 + 1) - 1) = 56287220785059466315505882940 := by
  have hlog : Nat.log2 (2 ^ (140 + 1) - 1) = 140 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (140 + 1) - 1) % 2 ^ 256 = 2 ^ (140 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_140_hi :
    model_ln_wad_evm (2 ^ (140 + 1)) = 56287220785059466315505882941 := by
  have hlog : Nat.log2 (2 ^ (140 + 1)) = 141 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (140 + 1)) % 2 ^ 256 = 2 ^ (140 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_140_lo :
    model_ln_wad_to_wad_evm (2 ^ (140 + 1) - 1) = 56287220785059466315 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (140 + 1) - 1) % 2 ^ 256 = 2 ^ (140 + 1) - 1 by decide]
  rw [ray_eval_seam_140_lo]
  decide

private theorem wad_eval_seam_140_hi :
    model_ln_wad_to_wad_evm (2 ^ (140 + 1)) = 56287220785059466315 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (140 + 1)) % 2 ^ 256 = 2 ^ (140 + 1) by decide]
  rw [ray_eval_seam_140_hi]
  decide

private theorem ray_seam_140 :
    sle (model_ln_wad_evm (2 ^ (140 + 1) - 1)) (model_ln_wad_evm (2 ^ (140 + 1))) = true := by
  rw [ray_eval_seam_140_lo, ray_eval_seam_140_hi]
  unfold sle
  decide

private theorem wad_seam_140 :
    sle (model_ln_wad_to_wad_evm (2 ^ (140 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (140 + 1))) = true := by
  rw [wad_eval_seam_140_lo, wad_eval_seam_140_hi]
  unfold sle
  decide

private theorem ray_eval_seam_141_lo :
    model_ln_wad_evm (2 ^ (141 + 1) - 1) = 56980367965619411624923115062 := by
  have hlog : Nat.log2 (2 ^ (141 + 1) - 1) = 141 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (141 + 1) - 1) % 2 ^ 256 = 2 ^ (141 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_141_hi :
    model_ln_wad_evm (2 ^ (141 + 1)) = 56980367965619411624923115062 := by
  have hlog : Nat.log2 (2 ^ (141 + 1)) = 142 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (141 + 1)) % 2 ^ 256 = 2 ^ (141 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_141_lo :
    model_ln_wad_to_wad_evm (2 ^ (141 + 1) - 1) = 56980367965619411624 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (141 + 1) - 1) % 2 ^ 256 = 2 ^ (141 + 1) - 1 by decide]
  rw [ray_eval_seam_141_lo]
  decide

private theorem wad_eval_seam_141_hi :
    model_ln_wad_to_wad_evm (2 ^ (141 + 1)) = 56980367965619411624 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (141 + 1)) % 2 ^ 256 = 2 ^ (141 + 1) by decide]
  rw [ray_eval_seam_141_hi]
  decide

private theorem ray_seam_141 :
    sle (model_ln_wad_evm (2 ^ (141 + 1) - 1)) (model_ln_wad_evm (2 ^ (141 + 1))) = true := by
  rw [ray_eval_seam_141_lo, ray_eval_seam_141_hi]
  unfold sle
  decide

private theorem wad_seam_141 :
    sle (model_ln_wad_to_wad_evm (2 ^ (141 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (141 + 1))) = true := by
  rw [wad_eval_seam_141_lo, wad_eval_seam_141_hi]
  unfold sle
  decide

private theorem ray_eval_seam_142_lo :
    model_ln_wad_evm (2 ^ (142 + 1) - 1) = 57673515146179356934340347183 := by
  have hlog : Nat.log2 (2 ^ (142 + 1) - 1) = 142 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (142 + 1) - 1) % 2 ^ 256 = 2 ^ (142 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_142_hi :
    model_ln_wad_evm (2 ^ (142 + 1)) = 57673515146179356934340347184 := by
  have hlog : Nat.log2 (2 ^ (142 + 1)) = 143 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (142 + 1)) % 2 ^ 256 = 2 ^ (142 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_142_lo :
    model_ln_wad_to_wad_evm (2 ^ (142 + 1) - 1) = 57673515146179356934 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (142 + 1) - 1) % 2 ^ 256 = 2 ^ (142 + 1) - 1 by decide]
  rw [ray_eval_seam_142_lo]
  decide

private theorem wad_eval_seam_142_hi :
    model_ln_wad_to_wad_evm (2 ^ (142 + 1)) = 57673515146179356934 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (142 + 1)) % 2 ^ 256 = 2 ^ (142 + 1) by decide]
  rw [ray_eval_seam_142_hi]
  decide

private theorem ray_seam_142 :
    sle (model_ln_wad_evm (2 ^ (142 + 1) - 1)) (model_ln_wad_evm (2 ^ (142 + 1))) = true := by
  rw [ray_eval_seam_142_lo, ray_eval_seam_142_hi]
  unfold sle
  decide

private theorem wad_seam_142 :
    sle (model_ln_wad_to_wad_evm (2 ^ (142 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (142 + 1))) = true := by
  rw [wad_eval_seam_142_lo, wad_eval_seam_142_hi]
  unfold sle
  decide

private theorem ray_eval_seam_143_lo :
    model_ln_wad_evm (2 ^ (143 + 1) - 1) = 58366662326739302243757579304 := by
  have hlog : Nat.log2 (2 ^ (143 + 1) - 1) = 143 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (143 + 1) - 1) % 2 ^ 256 = 2 ^ (143 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_143_hi :
    model_ln_wad_evm (2 ^ (143 + 1)) = 58366662326739302243757579305 := by
  have hlog : Nat.log2 (2 ^ (143 + 1)) = 144 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (143 + 1)) % 2 ^ 256 = 2 ^ (143 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_143_lo :
    model_ln_wad_to_wad_evm (2 ^ (143 + 1) - 1) = 58366662326739302243 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (143 + 1) - 1) % 2 ^ 256 = 2 ^ (143 + 1) - 1 by decide]
  rw [ray_eval_seam_143_lo]
  decide

private theorem wad_eval_seam_143_hi :
    model_ln_wad_to_wad_evm (2 ^ (143 + 1)) = 58366662326739302243 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (143 + 1)) % 2 ^ 256 = 2 ^ (143 + 1) by decide]
  rw [ray_eval_seam_143_hi]
  decide

private theorem ray_seam_143 :
    sle (model_ln_wad_evm (2 ^ (143 + 1) - 1)) (model_ln_wad_evm (2 ^ (143 + 1))) = true := by
  rw [ray_eval_seam_143_lo, ray_eval_seam_143_hi]
  unfold sle
  decide

private theorem wad_seam_143 :
    sle (model_ln_wad_to_wad_evm (2 ^ (143 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (143 + 1))) = true := by
  rw [wad_eval_seam_143_lo, wad_eval_seam_143_hi]
  unfold sle
  decide

private theorem ray_eval_seam_144_lo :
    model_ln_wad_evm (2 ^ (144 + 1) - 1) = 59059809507299247553174811426 := by
  have hlog : Nat.log2 (2 ^ (144 + 1) - 1) = 144 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (144 + 1) - 1) % 2 ^ 256 = 2 ^ (144 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_144_hi :
    model_ln_wad_evm (2 ^ (144 + 1)) = 59059809507299247553174811427 := by
  have hlog : Nat.log2 (2 ^ (144 + 1)) = 145 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (144 + 1)) % 2 ^ 256 = 2 ^ (144 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_144_lo :
    model_ln_wad_to_wad_evm (2 ^ (144 + 1) - 1) = 59059809507299247553 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (144 + 1) - 1) % 2 ^ 256 = 2 ^ (144 + 1) - 1 by decide]
  rw [ray_eval_seam_144_lo]
  decide

private theorem wad_eval_seam_144_hi :
    model_ln_wad_to_wad_evm (2 ^ (144 + 1)) = 59059809507299247553 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (144 + 1)) % 2 ^ 256 = 2 ^ (144 + 1) by decide]
  rw [ray_eval_seam_144_hi]
  decide

private theorem ray_seam_144 :
    sle (model_ln_wad_evm (2 ^ (144 + 1) - 1)) (model_ln_wad_evm (2 ^ (144 + 1))) = true := by
  rw [ray_eval_seam_144_lo, ray_eval_seam_144_hi]
  unfold sle
  decide

private theorem wad_seam_144 :
    sle (model_ln_wad_to_wad_evm (2 ^ (144 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (144 + 1))) = true := by
  rw [wad_eval_seam_144_lo, wad_eval_seam_144_hi]
  unfold sle
  decide

private theorem ray_eval_seam_145_lo :
    model_ln_wad_evm (2 ^ (145 + 1) - 1) = 59752956687859192862592043547 := by
  have hlog : Nat.log2 (2 ^ (145 + 1) - 1) = 145 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (145 + 1) - 1) % 2 ^ 256 = 2 ^ (145 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_145_hi :
    model_ln_wad_evm (2 ^ (145 + 1)) = 59752956687859192862592043548 := by
  have hlog : Nat.log2 (2 ^ (145 + 1)) = 146 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (145 + 1)) % 2 ^ 256 = 2 ^ (145 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_145_lo :
    model_ln_wad_to_wad_evm (2 ^ (145 + 1) - 1) = 59752956687859192862 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (145 + 1) - 1) % 2 ^ 256 = 2 ^ (145 + 1) - 1 by decide]
  rw [ray_eval_seam_145_lo]
  decide

private theorem wad_eval_seam_145_hi :
    model_ln_wad_to_wad_evm (2 ^ (145 + 1)) = 59752956687859192862 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (145 + 1)) % 2 ^ 256 = 2 ^ (145 + 1) by decide]
  rw [ray_eval_seam_145_hi]
  decide

private theorem ray_seam_145 :
    sle (model_ln_wad_evm (2 ^ (145 + 1) - 1)) (model_ln_wad_evm (2 ^ (145 + 1))) = true := by
  rw [ray_eval_seam_145_lo, ray_eval_seam_145_hi]
  unfold sle
  decide

private theorem wad_seam_145 :
    sle (model_ln_wad_to_wad_evm (2 ^ (145 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (145 + 1))) = true := by
  rw [wad_eval_seam_145_lo, wad_eval_seam_145_hi]
  unfold sle
  decide

private theorem ray_eval_seam_146_lo :
    model_ln_wad_evm (2 ^ (146 + 1) - 1) = 60446103868419138172009275669 := by
  have hlog : Nat.log2 (2 ^ (146 + 1) - 1) = 146 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (146 + 1) - 1) % 2 ^ 256 = 2 ^ (146 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_146_hi :
    model_ln_wad_evm (2 ^ (146 + 1)) = 60446103868419138172009275670 := by
  have hlog : Nat.log2 (2 ^ (146 + 1)) = 147 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (146 + 1)) % 2 ^ 256 = 2 ^ (146 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_146_lo :
    model_ln_wad_to_wad_evm (2 ^ (146 + 1) - 1) = 60446103868419138172 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (146 + 1) - 1) % 2 ^ 256 = 2 ^ (146 + 1) - 1 by decide]
  rw [ray_eval_seam_146_lo]
  decide

private theorem wad_eval_seam_146_hi :
    model_ln_wad_to_wad_evm (2 ^ (146 + 1)) = 60446103868419138172 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (146 + 1)) % 2 ^ 256 = 2 ^ (146 + 1) by decide]
  rw [ray_eval_seam_146_hi]
  decide

private theorem ray_seam_146 :
    sle (model_ln_wad_evm (2 ^ (146 + 1) - 1)) (model_ln_wad_evm (2 ^ (146 + 1))) = true := by
  rw [ray_eval_seam_146_lo, ray_eval_seam_146_hi]
  unfold sle
  decide

private theorem wad_seam_146 :
    sle (model_ln_wad_to_wad_evm (2 ^ (146 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (146 + 1))) = true := by
  rw [wad_eval_seam_146_lo, wad_eval_seam_146_hi]
  unfold sle
  decide

private theorem ray_eval_seam_147_lo :
    model_ln_wad_evm (2 ^ (147 + 1) - 1) = 61139251048979083481426507790 := by
  have hlog : Nat.log2 (2 ^ (147 + 1) - 1) = 147 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (147 + 1) - 1) % 2 ^ 256 = 2 ^ (147 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_147_hi :
    model_ln_wad_evm (2 ^ (147 + 1)) = 61139251048979083481426507791 := by
  have hlog : Nat.log2 (2 ^ (147 + 1)) = 148 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (147 + 1)) % 2 ^ 256 = 2 ^ (147 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_147_lo :
    model_ln_wad_to_wad_evm (2 ^ (147 + 1) - 1) = 61139251048979083481 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (147 + 1) - 1) % 2 ^ 256 = 2 ^ (147 + 1) - 1 by decide]
  rw [ray_eval_seam_147_lo]
  decide

private theorem wad_eval_seam_147_hi :
    model_ln_wad_to_wad_evm (2 ^ (147 + 1)) = 61139251048979083481 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (147 + 1)) % 2 ^ 256 = 2 ^ (147 + 1) by decide]
  rw [ray_eval_seam_147_hi]
  decide

private theorem ray_seam_147 :
    sle (model_ln_wad_evm (2 ^ (147 + 1) - 1)) (model_ln_wad_evm (2 ^ (147 + 1))) = true := by
  rw [ray_eval_seam_147_lo, ray_eval_seam_147_hi]
  unfold sle
  decide

private theorem wad_seam_147 :
    sle (model_ln_wad_to_wad_evm (2 ^ (147 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (147 + 1))) = true := by
  rw [wad_eval_seam_147_lo, wad_eval_seam_147_hi]
  unfold sle
  decide

private theorem ray_eval_seam_148_lo :
    model_ln_wad_evm (2 ^ (148 + 1) - 1) = 61832398229539028790843739912 := by
  have hlog : Nat.log2 (2 ^ (148 + 1) - 1) = 148 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (148 + 1) - 1) % 2 ^ 256 = 2 ^ (148 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_148_hi :
    model_ln_wad_evm (2 ^ (148 + 1)) = 61832398229539028790843739912 := by
  have hlog : Nat.log2 (2 ^ (148 + 1)) = 149 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (148 + 1)) % 2 ^ 256 = 2 ^ (148 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_148_lo :
    model_ln_wad_to_wad_evm (2 ^ (148 + 1) - 1) = 61832398229539028790 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (148 + 1) - 1) % 2 ^ 256 = 2 ^ (148 + 1) - 1 by decide]
  rw [ray_eval_seam_148_lo]
  decide

private theorem wad_eval_seam_148_hi :
    model_ln_wad_to_wad_evm (2 ^ (148 + 1)) = 61832398229539028790 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (148 + 1)) % 2 ^ 256 = 2 ^ (148 + 1) by decide]
  rw [ray_eval_seam_148_hi]
  decide

private theorem ray_seam_148 :
    sle (model_ln_wad_evm (2 ^ (148 + 1) - 1)) (model_ln_wad_evm (2 ^ (148 + 1))) = true := by
  rw [ray_eval_seam_148_lo, ray_eval_seam_148_hi]
  unfold sle
  decide

private theorem wad_seam_148 :
    sle (model_ln_wad_to_wad_evm (2 ^ (148 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (148 + 1))) = true := by
  rw [wad_eval_seam_148_lo, wad_eval_seam_148_hi]
  unfold sle
  decide

private theorem ray_eval_seam_149_lo :
    model_ln_wad_evm (2 ^ (149 + 1) - 1) = 62525545410098974100260972033 := by
  have hlog : Nat.log2 (2 ^ (149 + 1) - 1) = 149 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (149 + 1) - 1) % 2 ^ 256 = 2 ^ (149 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_149_hi :
    model_ln_wad_evm (2 ^ (149 + 1)) = 62525545410098974100260972034 := by
  have hlog : Nat.log2 (2 ^ (149 + 1)) = 150 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (149 + 1)) % 2 ^ 256 = 2 ^ (149 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_149_lo :
    model_ln_wad_to_wad_evm (2 ^ (149 + 1) - 1) = 62525545410098974100 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (149 + 1) - 1) % 2 ^ 256 = 2 ^ (149 + 1) - 1 by decide]
  rw [ray_eval_seam_149_lo]
  decide

private theorem wad_eval_seam_149_hi :
    model_ln_wad_to_wad_evm (2 ^ (149 + 1)) = 62525545410098974100 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (149 + 1)) % 2 ^ 256 = 2 ^ (149 + 1) by decide]
  rw [ray_eval_seam_149_hi]
  decide

private theorem ray_seam_149 :
    sle (model_ln_wad_evm (2 ^ (149 + 1) - 1)) (model_ln_wad_evm (2 ^ (149 + 1))) = true := by
  rw [ray_eval_seam_149_lo, ray_eval_seam_149_hi]
  unfold sle
  decide

private theorem wad_seam_149 :
    sle (model_ln_wad_to_wad_evm (2 ^ (149 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (149 + 1))) = true := by
  rw [wad_eval_seam_149_lo, wad_eval_seam_149_hi]
  unfold sle
  decide

private theorem ray_eval_seam_150_lo :
    model_ln_wad_evm (2 ^ (150 + 1) - 1) = 63218692590658919409678204155 := by
  have hlog : Nat.log2 (2 ^ (150 + 1) - 1) = 150 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (150 + 1) - 1) % 2 ^ 256 = 2 ^ (150 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_150_hi :
    model_ln_wad_evm (2 ^ (150 + 1)) = 63218692590658919409678204155 := by
  have hlog : Nat.log2 (2 ^ (150 + 1)) = 151 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (150 + 1)) % 2 ^ 256 = 2 ^ (150 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_150_lo :
    model_ln_wad_to_wad_evm (2 ^ (150 + 1) - 1) = 63218692590658919409 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (150 + 1) - 1) % 2 ^ 256 = 2 ^ (150 + 1) - 1 by decide]
  rw [ray_eval_seam_150_lo]
  decide

private theorem wad_eval_seam_150_hi :
    model_ln_wad_to_wad_evm (2 ^ (150 + 1)) = 63218692590658919409 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (150 + 1)) % 2 ^ 256 = 2 ^ (150 + 1) by decide]
  rw [ray_eval_seam_150_hi]
  decide

private theorem ray_seam_150 :
    sle (model_ln_wad_evm (2 ^ (150 + 1) - 1)) (model_ln_wad_evm (2 ^ (150 + 1))) = true := by
  rw [ray_eval_seam_150_lo, ray_eval_seam_150_hi]
  unfold sle
  decide

private theorem wad_seam_150 :
    sle (model_ln_wad_to_wad_evm (2 ^ (150 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (150 + 1))) = true := by
  rw [wad_eval_seam_150_lo, wad_eval_seam_150_hi]
  unfold sle
  decide

private theorem ray_eval_seam_151_lo :
    model_ln_wad_evm (2 ^ (151 + 1) - 1) = 63911839771218864719095436276 := by
  have hlog : Nat.log2 (2 ^ (151 + 1) - 1) = 151 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (151 + 1) - 1) % 2 ^ 256 = 2 ^ (151 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_151_hi :
    model_ln_wad_evm (2 ^ (151 + 1)) = 63911839771218864719095436277 := by
  have hlog : Nat.log2 (2 ^ (151 + 1)) = 152 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (151 + 1)) % 2 ^ 256 = 2 ^ (151 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_151_lo :
    model_ln_wad_to_wad_evm (2 ^ (151 + 1) - 1) = 63911839771218864719 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (151 + 1) - 1) % 2 ^ 256 = 2 ^ (151 + 1) - 1 by decide]
  rw [ray_eval_seam_151_lo]
  decide

private theorem wad_eval_seam_151_hi :
    model_ln_wad_to_wad_evm (2 ^ (151 + 1)) = 63911839771218864719 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (151 + 1)) % 2 ^ 256 = 2 ^ (151 + 1) by decide]
  rw [ray_eval_seam_151_hi]
  decide

private theorem ray_seam_151 :
    sle (model_ln_wad_evm (2 ^ (151 + 1) - 1)) (model_ln_wad_evm (2 ^ (151 + 1))) = true := by
  rw [ray_eval_seam_151_lo, ray_eval_seam_151_hi]
  unfold sle
  decide

private theorem wad_seam_151 :
    sle (model_ln_wad_to_wad_evm (2 ^ (151 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (151 + 1))) = true := by
  rw [wad_eval_seam_151_lo, wad_eval_seam_151_hi]
  unfold sle
  decide

private theorem ray_eval_seam_152_lo :
    model_ln_wad_evm (2 ^ (152 + 1) - 1) = 64604986951778810028512668398 := by
  have hlog : Nat.log2 (2 ^ (152 + 1) - 1) = 152 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (152 + 1) - 1) % 2 ^ 256 = 2 ^ (152 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_152_hi :
    model_ln_wad_evm (2 ^ (152 + 1)) = 64604986951778810028512668398 := by
  have hlog : Nat.log2 (2 ^ (152 + 1)) = 153 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (152 + 1)) % 2 ^ 256 = 2 ^ (152 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_152_lo :
    model_ln_wad_to_wad_evm (2 ^ (152 + 1) - 1) = 64604986951778810028 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (152 + 1) - 1) % 2 ^ 256 = 2 ^ (152 + 1) - 1 by decide]
  rw [ray_eval_seam_152_lo]
  decide

private theorem wad_eval_seam_152_hi :
    model_ln_wad_to_wad_evm (2 ^ (152 + 1)) = 64604986951778810028 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (152 + 1)) % 2 ^ 256 = 2 ^ (152 + 1) by decide]
  rw [ray_eval_seam_152_hi]
  decide

private theorem ray_seam_152 :
    sle (model_ln_wad_evm (2 ^ (152 + 1) - 1)) (model_ln_wad_evm (2 ^ (152 + 1))) = true := by
  rw [ray_eval_seam_152_lo, ray_eval_seam_152_hi]
  unfold sle
  decide

private theorem wad_seam_152 :
    sle (model_ln_wad_to_wad_evm (2 ^ (152 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (152 + 1))) = true := by
  rw [wad_eval_seam_152_lo, wad_eval_seam_152_hi]
  unfold sle
  decide

private theorem ray_eval_seam_153_lo :
    model_ln_wad_evm (2 ^ (153 + 1) - 1) = 65298134132338755337929900519 := by
  have hlog : Nat.log2 (2 ^ (153 + 1) - 1) = 153 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (153 + 1) - 1) % 2 ^ 256 = 2 ^ (153 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_153_hi :
    model_ln_wad_evm (2 ^ (153 + 1)) = 65298134132338755337929900520 := by
  have hlog : Nat.log2 (2 ^ (153 + 1)) = 154 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (153 + 1)) % 2 ^ 256 = 2 ^ (153 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_153_lo :
    model_ln_wad_to_wad_evm (2 ^ (153 + 1) - 1) = 65298134132338755337 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (153 + 1) - 1) % 2 ^ 256 = 2 ^ (153 + 1) - 1 by decide]
  rw [ray_eval_seam_153_lo]
  decide

private theorem wad_eval_seam_153_hi :
    model_ln_wad_to_wad_evm (2 ^ (153 + 1)) = 65298134132338755337 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (153 + 1)) % 2 ^ 256 = 2 ^ (153 + 1) by decide]
  rw [ray_eval_seam_153_hi]
  decide

private theorem ray_seam_153 :
    sle (model_ln_wad_evm (2 ^ (153 + 1) - 1)) (model_ln_wad_evm (2 ^ (153 + 1))) = true := by
  rw [ray_eval_seam_153_lo, ray_eval_seam_153_hi]
  unfold sle
  decide

private theorem wad_seam_153 :
    sle (model_ln_wad_to_wad_evm (2 ^ (153 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (153 + 1))) = true := by
  rw [wad_eval_seam_153_lo, wad_eval_seam_153_hi]
  unfold sle
  decide

private theorem ray_eval_seam_154_lo :
    model_ln_wad_evm (2 ^ (154 + 1) - 1) = 65991281312898700647347132641 := by
  have hlog : Nat.log2 (2 ^ (154 + 1) - 1) = 154 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (154 + 1) - 1) % 2 ^ 256 = 2 ^ (154 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_154_hi :
    model_ln_wad_evm (2 ^ (154 + 1)) = 65991281312898700647347132641 := by
  have hlog : Nat.log2 (2 ^ (154 + 1)) = 155 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (154 + 1)) % 2 ^ 256 = 2 ^ (154 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_154_lo :
    model_ln_wad_to_wad_evm (2 ^ (154 + 1) - 1) = 65991281312898700647 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (154 + 1) - 1) % 2 ^ 256 = 2 ^ (154 + 1) - 1 by decide]
  rw [ray_eval_seam_154_lo]
  decide

private theorem wad_eval_seam_154_hi :
    model_ln_wad_to_wad_evm (2 ^ (154 + 1)) = 65991281312898700647 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (154 + 1)) % 2 ^ 256 = 2 ^ (154 + 1) by decide]
  rw [ray_eval_seam_154_hi]
  decide

private theorem ray_seam_154 :
    sle (model_ln_wad_evm (2 ^ (154 + 1) - 1)) (model_ln_wad_evm (2 ^ (154 + 1))) = true := by
  rw [ray_eval_seam_154_lo, ray_eval_seam_154_hi]
  unfold sle
  decide

private theorem wad_seam_154 :
    sle (model_ln_wad_to_wad_evm (2 ^ (154 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (154 + 1))) = true := by
  rw [wad_eval_seam_154_lo, wad_eval_seam_154_hi]
  unfold sle
  decide

private theorem ray_eval_seam_155_lo :
    model_ln_wad_evm (2 ^ (155 + 1) - 1) = 66684428493458645956764364762 := by
  have hlog : Nat.log2 (2 ^ (155 + 1) - 1) = 155 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (155 + 1) - 1) % 2 ^ 256 = 2 ^ (155 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_155_hi :
    model_ln_wad_evm (2 ^ (155 + 1)) = 66684428493458645956764364763 := by
  have hlog : Nat.log2 (2 ^ (155 + 1)) = 156 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (155 + 1)) % 2 ^ 256 = 2 ^ (155 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_155_lo :
    model_ln_wad_to_wad_evm (2 ^ (155 + 1) - 1) = 66684428493458645956 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (155 + 1) - 1) % 2 ^ 256 = 2 ^ (155 + 1) - 1 by decide]
  rw [ray_eval_seam_155_lo]
  decide

private theorem wad_eval_seam_155_hi :
    model_ln_wad_to_wad_evm (2 ^ (155 + 1)) = 66684428493458645956 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (155 + 1)) % 2 ^ 256 = 2 ^ (155 + 1) by decide]
  rw [ray_eval_seam_155_hi]
  decide

private theorem ray_seam_155 :
    sle (model_ln_wad_evm (2 ^ (155 + 1) - 1)) (model_ln_wad_evm (2 ^ (155 + 1))) = true := by
  rw [ray_eval_seam_155_lo, ray_eval_seam_155_hi]
  unfold sle
  decide

private theorem wad_seam_155 :
    sle (model_ln_wad_to_wad_evm (2 ^ (155 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (155 + 1))) = true := by
  rw [wad_eval_seam_155_lo, wad_eval_seam_155_hi]
  unfold sle
  decide

private theorem ray_eval_seam_156_lo :
    model_ln_wad_evm (2 ^ (156 + 1) - 1) = 67377575674018591266181596883 := by
  have hlog : Nat.log2 (2 ^ (156 + 1) - 1) = 156 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (156 + 1) - 1) % 2 ^ 256 = 2 ^ (156 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_156_hi :
    model_ln_wad_evm (2 ^ (156 + 1)) = 67377575674018591266181596884 := by
  have hlog : Nat.log2 (2 ^ (156 + 1)) = 157 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (156 + 1)) % 2 ^ 256 = 2 ^ (156 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_156_lo :
    model_ln_wad_to_wad_evm (2 ^ (156 + 1) - 1) = 67377575674018591266 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (156 + 1) - 1) % 2 ^ 256 = 2 ^ (156 + 1) - 1 by decide]
  rw [ray_eval_seam_156_lo]
  decide

private theorem wad_eval_seam_156_hi :
    model_ln_wad_to_wad_evm (2 ^ (156 + 1)) = 67377575674018591266 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (156 + 1)) % 2 ^ 256 = 2 ^ (156 + 1) by decide]
  rw [ray_eval_seam_156_hi]
  decide

private theorem ray_seam_156 :
    sle (model_ln_wad_evm (2 ^ (156 + 1) - 1)) (model_ln_wad_evm (2 ^ (156 + 1))) = true := by
  rw [ray_eval_seam_156_lo, ray_eval_seam_156_hi]
  unfold sle
  decide

private theorem wad_seam_156 :
    sle (model_ln_wad_to_wad_evm (2 ^ (156 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (156 + 1))) = true := by
  rw [wad_eval_seam_156_lo, wad_eval_seam_156_hi]
  unfold sle
  decide

private theorem ray_eval_seam_157_lo :
    model_ln_wad_evm (2 ^ (157 + 1) - 1) = 68070722854578536575598829005 := by
  have hlog : Nat.log2 (2 ^ (157 + 1) - 1) = 157 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (157 + 1) - 1) % 2 ^ 256 = 2 ^ (157 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_157_hi :
    model_ln_wad_evm (2 ^ (157 + 1)) = 68070722854578536575598829006 := by
  have hlog : Nat.log2 (2 ^ (157 + 1)) = 158 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (157 + 1)) % 2 ^ 256 = 2 ^ (157 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_157_lo :
    model_ln_wad_to_wad_evm (2 ^ (157 + 1) - 1) = 68070722854578536575 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (157 + 1) - 1) % 2 ^ 256 = 2 ^ (157 + 1) - 1 by decide]
  rw [ray_eval_seam_157_lo]
  decide

private theorem wad_eval_seam_157_hi :
    model_ln_wad_to_wad_evm (2 ^ (157 + 1)) = 68070722854578536575 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (157 + 1)) % 2 ^ 256 = 2 ^ (157 + 1) by decide]
  rw [ray_eval_seam_157_hi]
  decide

private theorem ray_seam_157 :
    sle (model_ln_wad_evm (2 ^ (157 + 1) - 1)) (model_ln_wad_evm (2 ^ (157 + 1))) = true := by
  rw [ray_eval_seam_157_lo, ray_eval_seam_157_hi]
  unfold sle
  decide

private theorem wad_seam_157 :
    sle (model_ln_wad_to_wad_evm (2 ^ (157 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (157 + 1))) = true := by
  rw [wad_eval_seam_157_lo, wad_eval_seam_157_hi]
  unfold sle
  decide

private theorem ray_eval_seam_158_lo :
    model_ln_wad_evm (2 ^ (158 + 1) - 1) = 68763870035138481885016061126 := by
  have hlog : Nat.log2 (2 ^ (158 + 1) - 1) = 158 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (158 + 1) - 1) % 2 ^ 256 = 2 ^ (158 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_158_hi :
    model_ln_wad_evm (2 ^ (158 + 1)) = 68763870035138481885016061127 := by
  have hlog : Nat.log2 (2 ^ (158 + 1)) = 159 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (158 + 1)) % 2 ^ 256 = 2 ^ (158 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_158_lo :
    model_ln_wad_to_wad_evm (2 ^ (158 + 1) - 1) = 68763870035138481885 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (158 + 1) - 1) % 2 ^ 256 = 2 ^ (158 + 1) - 1 by decide]
  rw [ray_eval_seam_158_lo]
  decide

private theorem wad_eval_seam_158_hi :
    model_ln_wad_to_wad_evm (2 ^ (158 + 1)) = 68763870035138481885 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (158 + 1)) % 2 ^ 256 = 2 ^ (158 + 1) by decide]
  rw [ray_eval_seam_158_hi]
  decide

private theorem ray_seam_158 :
    sle (model_ln_wad_evm (2 ^ (158 + 1) - 1)) (model_ln_wad_evm (2 ^ (158 + 1))) = true := by
  rw [ray_eval_seam_158_lo, ray_eval_seam_158_hi]
  unfold sle
  decide

private theorem wad_seam_158 :
    sle (model_ln_wad_to_wad_evm (2 ^ (158 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (158 + 1))) = true := by
  rw [wad_eval_seam_158_lo, wad_eval_seam_158_hi]
  unfold sle
  decide

private theorem ray_eval_seam_159_lo :
    model_ln_wad_evm (2 ^ (159 + 1) - 1) = 69457017215698427194433293248 := by
  have hlog : Nat.log2 (2 ^ (159 + 1) - 1) = 159 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (159 + 1) - 1) % 2 ^ 256 = 2 ^ (159 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_159_hi :
    model_ln_wad_evm (2 ^ (159 + 1)) = 69457017215698427194433293248 := by
  have hlog : Nat.log2 (2 ^ (159 + 1)) = 160 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (159 + 1)) % 2 ^ 256 = 2 ^ (159 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_159_lo :
    model_ln_wad_to_wad_evm (2 ^ (159 + 1) - 1) = 69457017215698427194 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (159 + 1) - 1) % 2 ^ 256 = 2 ^ (159 + 1) - 1 by decide]
  rw [ray_eval_seam_159_lo]
  decide

private theorem wad_eval_seam_159_hi :
    model_ln_wad_to_wad_evm (2 ^ (159 + 1)) = 69457017215698427194 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (159 + 1)) % 2 ^ 256 = 2 ^ (159 + 1) by decide]
  rw [ray_eval_seam_159_hi]
  decide

private theorem ray_seam_159 :
    sle (model_ln_wad_evm (2 ^ (159 + 1) - 1)) (model_ln_wad_evm (2 ^ (159 + 1))) = true := by
  rw [ray_eval_seam_159_lo, ray_eval_seam_159_hi]
  unfold sle
  decide

private theorem wad_seam_159 :
    sle (model_ln_wad_to_wad_evm (2 ^ (159 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (159 + 1))) = true := by
  rw [wad_eval_seam_159_lo, wad_eval_seam_159_hi]
  unfold sle
  decide

private theorem ray_eval_seam_160_lo :
    model_ln_wad_evm (2 ^ (160 + 1) - 1) = 70150164396258372503850525369 := by
  have hlog : Nat.log2 (2 ^ (160 + 1) - 1) = 160 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (160 + 1) - 1) % 2 ^ 256 = 2 ^ (160 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_160_hi :
    model_ln_wad_evm (2 ^ (160 + 1)) = 70150164396258372503850525370 := by
  have hlog : Nat.log2 (2 ^ (160 + 1)) = 161 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (160 + 1)) % 2 ^ 256 = 2 ^ (160 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_160_lo :
    model_ln_wad_to_wad_evm (2 ^ (160 + 1) - 1) = 70150164396258372503 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (160 + 1) - 1) % 2 ^ 256 = 2 ^ (160 + 1) - 1 by decide]
  rw [ray_eval_seam_160_lo]
  decide

private theorem wad_eval_seam_160_hi :
    model_ln_wad_to_wad_evm (2 ^ (160 + 1)) = 70150164396258372503 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (160 + 1)) % 2 ^ 256 = 2 ^ (160 + 1) by decide]
  rw [ray_eval_seam_160_hi]
  decide

private theorem ray_seam_160 :
    sle (model_ln_wad_evm (2 ^ (160 + 1) - 1)) (model_ln_wad_evm (2 ^ (160 + 1))) = true := by
  rw [ray_eval_seam_160_lo, ray_eval_seam_160_hi]
  unfold sle
  decide

private theorem wad_seam_160 :
    sle (model_ln_wad_to_wad_evm (2 ^ (160 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (160 + 1))) = true := by
  rw [wad_eval_seam_160_lo, wad_eval_seam_160_hi]
  unfold sle
  decide

private theorem ray_eval_seam_161_lo :
    model_ln_wad_evm (2 ^ (161 + 1) - 1) = 70843311576818317813267757491 := by
  have hlog : Nat.log2 (2 ^ (161 + 1) - 1) = 161 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (161 + 1) - 1) % 2 ^ 256 = 2 ^ (161 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_161_hi :
    model_ln_wad_evm (2 ^ (161 + 1)) = 70843311576818317813267757491 := by
  have hlog : Nat.log2 (2 ^ (161 + 1)) = 162 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (161 + 1)) % 2 ^ 256 = 2 ^ (161 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_161_lo :
    model_ln_wad_to_wad_evm (2 ^ (161 + 1) - 1) = 70843311576818317813 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (161 + 1) - 1) % 2 ^ 256 = 2 ^ (161 + 1) - 1 by decide]
  rw [ray_eval_seam_161_lo]
  decide

private theorem wad_eval_seam_161_hi :
    model_ln_wad_to_wad_evm (2 ^ (161 + 1)) = 70843311576818317813 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (161 + 1)) % 2 ^ 256 = 2 ^ (161 + 1) by decide]
  rw [ray_eval_seam_161_hi]
  decide

private theorem ray_seam_161 :
    sle (model_ln_wad_evm (2 ^ (161 + 1) - 1)) (model_ln_wad_evm (2 ^ (161 + 1))) = true := by
  rw [ray_eval_seam_161_lo, ray_eval_seam_161_hi]
  unfold sle
  decide

private theorem wad_seam_161 :
    sle (model_ln_wad_to_wad_evm (2 ^ (161 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (161 + 1))) = true := by
  rw [wad_eval_seam_161_lo, wad_eval_seam_161_hi]
  unfold sle
  decide

private theorem ray_eval_seam_162_lo :
    model_ln_wad_evm (2 ^ (162 + 1) - 1) = 71536458757378263122684989612 := by
  have hlog : Nat.log2 (2 ^ (162 + 1) - 1) = 162 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (162 + 1) - 1) % 2 ^ 256 = 2 ^ (162 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_162_hi :
    model_ln_wad_evm (2 ^ (162 + 1)) = 71536458757378263122684989613 := by
  have hlog : Nat.log2 (2 ^ (162 + 1)) = 163 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (162 + 1)) % 2 ^ 256 = 2 ^ (162 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_162_lo :
    model_ln_wad_to_wad_evm (2 ^ (162 + 1) - 1) = 71536458757378263122 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (162 + 1) - 1) % 2 ^ 256 = 2 ^ (162 + 1) - 1 by decide]
  rw [ray_eval_seam_162_lo]
  decide

private theorem wad_eval_seam_162_hi :
    model_ln_wad_to_wad_evm (2 ^ (162 + 1)) = 71536458757378263122 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (162 + 1)) % 2 ^ 256 = 2 ^ (162 + 1) by decide]
  rw [ray_eval_seam_162_hi]
  decide

private theorem ray_seam_162 :
    sle (model_ln_wad_evm (2 ^ (162 + 1) - 1)) (model_ln_wad_evm (2 ^ (162 + 1))) = true := by
  rw [ray_eval_seam_162_lo, ray_eval_seam_162_hi]
  unfold sle
  decide

private theorem wad_seam_162 :
    sle (model_ln_wad_to_wad_evm (2 ^ (162 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (162 + 1))) = true := by
  rw [wad_eval_seam_162_lo, wad_eval_seam_162_hi]
  unfold sle
  decide

private theorem ray_eval_seam_163_lo :
    model_ln_wad_evm (2 ^ (163 + 1) - 1) = 72229605937938208432102221734 := by
  have hlog : Nat.log2 (2 ^ (163 + 1) - 1) = 163 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (163 + 1) - 1) % 2 ^ 256 = 2 ^ (163 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_163_hi :
    model_ln_wad_evm (2 ^ (163 + 1)) = 72229605937938208432102221734 := by
  have hlog : Nat.log2 (2 ^ (163 + 1)) = 164 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (163 + 1)) % 2 ^ 256 = 2 ^ (163 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_163_lo :
    model_ln_wad_to_wad_evm (2 ^ (163 + 1) - 1) = 72229605937938208432 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (163 + 1) - 1) % 2 ^ 256 = 2 ^ (163 + 1) - 1 by decide]
  rw [ray_eval_seam_163_lo]
  decide

private theorem wad_eval_seam_163_hi :
    model_ln_wad_to_wad_evm (2 ^ (163 + 1)) = 72229605937938208432 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (163 + 1)) % 2 ^ 256 = 2 ^ (163 + 1) by decide]
  rw [ray_eval_seam_163_hi]
  decide

private theorem ray_seam_163 :
    sle (model_ln_wad_evm (2 ^ (163 + 1) - 1)) (model_ln_wad_evm (2 ^ (163 + 1))) = true := by
  rw [ray_eval_seam_163_lo, ray_eval_seam_163_hi]
  unfold sle
  decide

private theorem wad_seam_163 :
    sle (model_ln_wad_to_wad_evm (2 ^ (163 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (163 + 1))) = true := by
  rw [wad_eval_seam_163_lo, wad_eval_seam_163_hi]
  unfold sle
  decide

private theorem ray_eval_seam_164_lo :
    model_ln_wad_evm (2 ^ (164 + 1) - 1) = 72922753118498153741519453855 := by
  have hlog : Nat.log2 (2 ^ (164 + 1) - 1) = 164 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (164 + 1) - 1) % 2 ^ 256 = 2 ^ (164 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_164_hi :
    model_ln_wad_evm (2 ^ (164 + 1)) = 72922753118498153741519453856 := by
  have hlog : Nat.log2 (2 ^ (164 + 1)) = 165 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (164 + 1)) % 2 ^ 256 = 2 ^ (164 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_164_lo :
    model_ln_wad_to_wad_evm (2 ^ (164 + 1) - 1) = 72922753118498153741 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (164 + 1) - 1) % 2 ^ 256 = 2 ^ (164 + 1) - 1 by decide]
  rw [ray_eval_seam_164_lo]
  decide

private theorem wad_eval_seam_164_hi :
    model_ln_wad_to_wad_evm (2 ^ (164 + 1)) = 72922753118498153741 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (164 + 1)) % 2 ^ 256 = 2 ^ (164 + 1) by decide]
  rw [ray_eval_seam_164_hi]
  decide

private theorem ray_seam_164 :
    sle (model_ln_wad_evm (2 ^ (164 + 1) - 1)) (model_ln_wad_evm (2 ^ (164 + 1))) = true := by
  rw [ray_eval_seam_164_lo, ray_eval_seam_164_hi]
  unfold sle
  decide

private theorem wad_seam_164 :
    sle (model_ln_wad_to_wad_evm (2 ^ (164 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (164 + 1))) = true := by
  rw [wad_eval_seam_164_lo, wad_eval_seam_164_hi]
  unfold sle
  decide

private theorem ray_eval_seam_165_lo :
    model_ln_wad_evm (2 ^ (165 + 1) - 1) = 73615900299058099050936685977 := by
  have hlog : Nat.log2 (2 ^ (165 + 1) - 1) = 165 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (165 + 1) - 1) % 2 ^ 256 = 2 ^ (165 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_165_hi :
    model_ln_wad_evm (2 ^ (165 + 1)) = 73615900299058099050936685977 := by
  have hlog : Nat.log2 (2 ^ (165 + 1)) = 166 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (165 + 1)) % 2 ^ 256 = 2 ^ (165 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_165_lo :
    model_ln_wad_to_wad_evm (2 ^ (165 + 1) - 1) = 73615900299058099050 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (165 + 1) - 1) % 2 ^ 256 = 2 ^ (165 + 1) - 1 by decide]
  rw [ray_eval_seam_165_lo]
  decide

private theorem wad_eval_seam_165_hi :
    model_ln_wad_to_wad_evm (2 ^ (165 + 1)) = 73615900299058099050 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (165 + 1)) % 2 ^ 256 = 2 ^ (165 + 1) by decide]
  rw [ray_eval_seam_165_hi]
  decide

private theorem ray_seam_165 :
    sle (model_ln_wad_evm (2 ^ (165 + 1) - 1)) (model_ln_wad_evm (2 ^ (165 + 1))) = true := by
  rw [ray_eval_seam_165_lo, ray_eval_seam_165_hi]
  unfold sle
  decide

private theorem wad_seam_165 :
    sle (model_ln_wad_to_wad_evm (2 ^ (165 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (165 + 1))) = true := by
  rw [wad_eval_seam_165_lo, wad_eval_seam_165_hi]
  unfold sle
  decide

private theorem ray_eval_seam_166_lo :
    model_ln_wad_evm (2 ^ (166 + 1) - 1) = 74309047479618044360353918098 := by
  have hlog : Nat.log2 (2 ^ (166 + 1) - 1) = 166 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (166 + 1) - 1) % 2 ^ 256 = 2 ^ (166 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_166_hi :
    model_ln_wad_evm (2 ^ (166 + 1)) = 74309047479618044360353918099 := by
  have hlog : Nat.log2 (2 ^ (166 + 1)) = 167 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (166 + 1)) % 2 ^ 256 = 2 ^ (166 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_166_lo :
    model_ln_wad_to_wad_evm (2 ^ (166 + 1) - 1) = 74309047479618044360 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (166 + 1) - 1) % 2 ^ 256 = 2 ^ (166 + 1) - 1 by decide]
  rw [ray_eval_seam_166_lo]
  decide

private theorem wad_eval_seam_166_hi :
    model_ln_wad_to_wad_evm (2 ^ (166 + 1)) = 74309047479618044360 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (166 + 1)) % 2 ^ 256 = 2 ^ (166 + 1) by decide]
  rw [ray_eval_seam_166_hi]
  decide

private theorem ray_seam_166 :
    sle (model_ln_wad_evm (2 ^ (166 + 1) - 1)) (model_ln_wad_evm (2 ^ (166 + 1))) = true := by
  rw [ray_eval_seam_166_lo, ray_eval_seam_166_hi]
  unfold sle
  decide

private theorem wad_seam_166 :
    sle (model_ln_wad_to_wad_evm (2 ^ (166 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (166 + 1))) = true := by
  rw [wad_eval_seam_166_lo, wad_eval_seam_166_hi]
  unfold sle
  decide

private theorem ray_eval_seam_167_lo :
    model_ln_wad_evm (2 ^ (167 + 1) - 1) = 75002194660177989669771150219 := by
  have hlog : Nat.log2 (2 ^ (167 + 1) - 1) = 167 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (167 + 1) - 1) % 2 ^ 256 = 2 ^ (167 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_167_hi :
    model_ln_wad_evm (2 ^ (167 + 1)) = 75002194660177989669771150220 := by
  have hlog : Nat.log2 (2 ^ (167 + 1)) = 168 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (167 + 1)) % 2 ^ 256 = 2 ^ (167 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_167_lo :
    model_ln_wad_to_wad_evm (2 ^ (167 + 1) - 1) = 75002194660177989669 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (167 + 1) - 1) % 2 ^ 256 = 2 ^ (167 + 1) - 1 by decide]
  rw [ray_eval_seam_167_lo]
  decide

private theorem wad_eval_seam_167_hi :
    model_ln_wad_to_wad_evm (2 ^ (167 + 1)) = 75002194660177989669 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (167 + 1)) % 2 ^ 256 = 2 ^ (167 + 1) by decide]
  rw [ray_eval_seam_167_hi]
  decide

private theorem ray_seam_167 :
    sle (model_ln_wad_evm (2 ^ (167 + 1) - 1)) (model_ln_wad_evm (2 ^ (167 + 1))) = true := by
  rw [ray_eval_seam_167_lo, ray_eval_seam_167_hi]
  unfold sle
  decide

private theorem wad_seam_167 :
    sle (model_ln_wad_to_wad_evm (2 ^ (167 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (167 + 1))) = true := by
  rw [wad_eval_seam_167_lo, wad_eval_seam_167_hi]
  unfold sle
  decide

private theorem ray_eval_seam_168_lo :
    model_ln_wad_evm (2 ^ (168 + 1) - 1) = 75695341840737934979188382341 := by
  have hlog : Nat.log2 (2 ^ (168 + 1) - 1) = 168 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (168 + 1) - 1) % 2 ^ 256 = 2 ^ (168 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_168_hi :
    model_ln_wad_evm (2 ^ (168 + 1)) = 75695341840737934979188382342 := by
  have hlog : Nat.log2 (2 ^ (168 + 1)) = 169 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (168 + 1)) % 2 ^ 256 = 2 ^ (168 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_168_lo :
    model_ln_wad_to_wad_evm (2 ^ (168 + 1) - 1) = 75695341840737934979 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (168 + 1) - 1) % 2 ^ 256 = 2 ^ (168 + 1) - 1 by decide]
  rw [ray_eval_seam_168_lo]
  decide

private theorem wad_eval_seam_168_hi :
    model_ln_wad_to_wad_evm (2 ^ (168 + 1)) = 75695341840737934979 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (168 + 1)) % 2 ^ 256 = 2 ^ (168 + 1) by decide]
  rw [ray_eval_seam_168_hi]
  decide

private theorem ray_seam_168 :
    sle (model_ln_wad_evm (2 ^ (168 + 1) - 1)) (model_ln_wad_evm (2 ^ (168 + 1))) = true := by
  rw [ray_eval_seam_168_lo, ray_eval_seam_168_hi]
  unfold sle
  decide

private theorem wad_seam_168 :
    sle (model_ln_wad_to_wad_evm (2 ^ (168 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (168 + 1))) = true := by
  rw [wad_eval_seam_168_lo, wad_eval_seam_168_hi]
  unfold sle
  decide

private theorem ray_eval_seam_169_lo :
    model_ln_wad_evm (2 ^ (169 + 1) - 1) = 76388489021297880288605614462 := by
  have hlog : Nat.log2 (2 ^ (169 + 1) - 1) = 169 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (169 + 1) - 1) % 2 ^ 256 = 2 ^ (169 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_169_hi :
    model_ln_wad_evm (2 ^ (169 + 1)) = 76388489021297880288605614463 := by
  have hlog : Nat.log2 (2 ^ (169 + 1)) = 170 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (169 + 1)) % 2 ^ 256 = 2 ^ (169 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_169_lo :
    model_ln_wad_to_wad_evm (2 ^ (169 + 1) - 1) = 76388489021297880288 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (169 + 1) - 1) % 2 ^ 256 = 2 ^ (169 + 1) - 1 by decide]
  rw [ray_eval_seam_169_lo]
  decide

private theorem wad_eval_seam_169_hi :
    model_ln_wad_to_wad_evm (2 ^ (169 + 1)) = 76388489021297880288 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (169 + 1)) % 2 ^ 256 = 2 ^ (169 + 1) by decide]
  rw [ray_eval_seam_169_hi]
  decide

private theorem ray_seam_169 :
    sle (model_ln_wad_evm (2 ^ (169 + 1) - 1)) (model_ln_wad_evm (2 ^ (169 + 1))) = true := by
  rw [ray_eval_seam_169_lo, ray_eval_seam_169_hi]
  unfold sle
  decide

private theorem wad_seam_169 :
    sle (model_ln_wad_to_wad_evm (2 ^ (169 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (169 + 1))) = true := by
  rw [wad_eval_seam_169_lo, wad_eval_seam_169_hi]
  unfold sle
  decide

private theorem ray_eval_seam_170_lo :
    model_ln_wad_evm (2 ^ (170 + 1) - 1) = 77081636201857825598022846584 := by
  have hlog : Nat.log2 (2 ^ (170 + 1) - 1) = 170 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (170 + 1) - 1) % 2 ^ 256 = 2 ^ (170 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_170_hi :
    model_ln_wad_evm (2 ^ (170 + 1)) = 77081636201857825598022846585 := by
  have hlog : Nat.log2 (2 ^ (170 + 1)) = 171 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (170 + 1)) % 2 ^ 256 = 2 ^ (170 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_170_lo :
    model_ln_wad_to_wad_evm (2 ^ (170 + 1) - 1) = 77081636201857825598 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (170 + 1) - 1) % 2 ^ 256 = 2 ^ (170 + 1) - 1 by decide]
  rw [ray_eval_seam_170_lo]
  decide

private theorem wad_eval_seam_170_hi :
    model_ln_wad_to_wad_evm (2 ^ (170 + 1)) = 77081636201857825598 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (170 + 1)) % 2 ^ 256 = 2 ^ (170 + 1) by decide]
  rw [ray_eval_seam_170_hi]
  decide

private theorem ray_seam_170 :
    sle (model_ln_wad_evm (2 ^ (170 + 1) - 1)) (model_ln_wad_evm (2 ^ (170 + 1))) = true := by
  rw [ray_eval_seam_170_lo, ray_eval_seam_170_hi]
  unfold sle
  decide

private theorem wad_seam_170 :
    sle (model_ln_wad_to_wad_evm (2 ^ (170 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (170 + 1))) = true := by
  rw [wad_eval_seam_170_lo, wad_eval_seam_170_hi]
  unfold sle
  decide

private theorem ray_eval_seam_171_lo :
    model_ln_wad_evm (2 ^ (171 + 1) - 1) = 77774783382417770907440078705 := by
  have hlog : Nat.log2 (2 ^ (171 + 1) - 1) = 171 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (171 + 1) - 1) % 2 ^ 256 = 2 ^ (171 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_171_hi :
    model_ln_wad_evm (2 ^ (171 + 1)) = 77774783382417770907440078706 := by
  have hlog : Nat.log2 (2 ^ (171 + 1)) = 172 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (171 + 1)) % 2 ^ 256 = 2 ^ (171 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_171_lo :
    model_ln_wad_to_wad_evm (2 ^ (171 + 1) - 1) = 77774783382417770907 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (171 + 1) - 1) % 2 ^ 256 = 2 ^ (171 + 1) - 1 by decide]
  rw [ray_eval_seam_171_lo]
  decide

private theorem wad_eval_seam_171_hi :
    model_ln_wad_to_wad_evm (2 ^ (171 + 1)) = 77774783382417770907 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (171 + 1)) % 2 ^ 256 = 2 ^ (171 + 1) by decide]
  rw [ray_eval_seam_171_hi]
  decide

private theorem ray_seam_171 :
    sle (model_ln_wad_evm (2 ^ (171 + 1) - 1)) (model_ln_wad_evm (2 ^ (171 + 1))) = true := by
  rw [ray_eval_seam_171_lo, ray_eval_seam_171_hi]
  unfold sle
  decide

private theorem wad_seam_171 :
    sle (model_ln_wad_to_wad_evm (2 ^ (171 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (171 + 1))) = true := by
  rw [wad_eval_seam_171_lo, wad_eval_seam_171_hi]
  unfold sle
  decide

private theorem ray_eval_seam_172_lo :
    model_ln_wad_evm (2 ^ (172 + 1) - 1) = 78467930562977716216857310827 := by
  have hlog : Nat.log2 (2 ^ (172 + 1) - 1) = 172 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (172 + 1) - 1) % 2 ^ 256 = 2 ^ (172 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_172_hi :
    model_ln_wad_evm (2 ^ (172 + 1)) = 78467930562977716216857310827 := by
  have hlog : Nat.log2 (2 ^ (172 + 1)) = 173 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (172 + 1)) % 2 ^ 256 = 2 ^ (172 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_172_lo :
    model_ln_wad_to_wad_evm (2 ^ (172 + 1) - 1) = 78467930562977716216 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (172 + 1) - 1) % 2 ^ 256 = 2 ^ (172 + 1) - 1 by decide]
  rw [ray_eval_seam_172_lo]
  decide

private theorem wad_eval_seam_172_hi :
    model_ln_wad_to_wad_evm (2 ^ (172 + 1)) = 78467930562977716216 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (172 + 1)) % 2 ^ 256 = 2 ^ (172 + 1) by decide]
  rw [ray_eval_seam_172_hi]
  decide

private theorem ray_seam_172 :
    sle (model_ln_wad_evm (2 ^ (172 + 1) - 1)) (model_ln_wad_evm (2 ^ (172 + 1))) = true := by
  rw [ray_eval_seam_172_lo, ray_eval_seam_172_hi]
  unfold sle
  decide

private theorem wad_seam_172 :
    sle (model_ln_wad_to_wad_evm (2 ^ (172 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (172 + 1))) = true := by
  rw [wad_eval_seam_172_lo, wad_eval_seam_172_hi]
  unfold sle
  decide

private theorem ray_eval_seam_173_lo :
    model_ln_wad_evm (2 ^ (173 + 1) - 1) = 79161077743537661526274542948 := by
  have hlog : Nat.log2 (2 ^ (173 + 1) - 1) = 173 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (173 + 1) - 1) % 2 ^ 256 = 2 ^ (173 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_173_hi :
    model_ln_wad_evm (2 ^ (173 + 1)) = 79161077743537661526274542949 := by
  have hlog : Nat.log2 (2 ^ (173 + 1)) = 174 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (173 + 1)) % 2 ^ 256 = 2 ^ (173 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_173_lo :
    model_ln_wad_to_wad_evm (2 ^ (173 + 1) - 1) = 79161077743537661526 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (173 + 1) - 1) % 2 ^ 256 = 2 ^ (173 + 1) - 1 by decide]
  rw [ray_eval_seam_173_lo]
  decide

private theorem wad_eval_seam_173_hi :
    model_ln_wad_to_wad_evm (2 ^ (173 + 1)) = 79161077743537661526 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (173 + 1)) % 2 ^ 256 = 2 ^ (173 + 1) by decide]
  rw [ray_eval_seam_173_hi]
  decide

private theorem ray_seam_173 :
    sle (model_ln_wad_evm (2 ^ (173 + 1) - 1)) (model_ln_wad_evm (2 ^ (173 + 1))) = true := by
  rw [ray_eval_seam_173_lo, ray_eval_seam_173_hi]
  unfold sle
  decide

private theorem wad_seam_173 :
    sle (model_ln_wad_to_wad_evm (2 ^ (173 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (173 + 1))) = true := by
  rw [wad_eval_seam_173_lo, wad_eval_seam_173_hi]
  unfold sle
  decide

private theorem ray_eval_seam_174_lo :
    model_ln_wad_evm (2 ^ (174 + 1) - 1) = 79854224924097606835691775070 := by
  have hlog : Nat.log2 (2 ^ (174 + 1) - 1) = 174 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (174 + 1) - 1) % 2 ^ 256 = 2 ^ (174 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_174_hi :
    model_ln_wad_evm (2 ^ (174 + 1)) = 79854224924097606835691775070 := by
  have hlog : Nat.log2 (2 ^ (174 + 1)) = 175 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (174 + 1)) % 2 ^ 256 = 2 ^ (174 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_174_lo :
    model_ln_wad_to_wad_evm (2 ^ (174 + 1) - 1) = 79854224924097606835 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (174 + 1) - 1) % 2 ^ 256 = 2 ^ (174 + 1) - 1 by decide]
  rw [ray_eval_seam_174_lo]
  decide

private theorem wad_eval_seam_174_hi :
    model_ln_wad_to_wad_evm (2 ^ (174 + 1)) = 79854224924097606835 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (174 + 1)) % 2 ^ 256 = 2 ^ (174 + 1) by decide]
  rw [ray_eval_seam_174_hi]
  decide

private theorem ray_seam_174 :
    sle (model_ln_wad_evm (2 ^ (174 + 1) - 1)) (model_ln_wad_evm (2 ^ (174 + 1))) = true := by
  rw [ray_eval_seam_174_lo, ray_eval_seam_174_hi]
  unfold sle
  decide

private theorem wad_seam_174 :
    sle (model_ln_wad_to_wad_evm (2 ^ (174 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (174 + 1))) = true := by
  rw [wad_eval_seam_174_lo, wad_eval_seam_174_hi]
  unfold sle
  decide

private theorem ray_eval_seam_175_lo :
    model_ln_wad_evm (2 ^ (175 + 1) - 1) = 80547372104657552145109007191 := by
  have hlog : Nat.log2 (2 ^ (175 + 1) - 1) = 175 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (175 + 1) - 1) % 2 ^ 256 = 2 ^ (175 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_175_hi :
    model_ln_wad_evm (2 ^ (175 + 1)) = 80547372104657552145109007192 := by
  have hlog : Nat.log2 (2 ^ (175 + 1)) = 176 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (175 + 1)) % 2 ^ 256 = 2 ^ (175 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_175_lo :
    model_ln_wad_to_wad_evm (2 ^ (175 + 1) - 1) = 80547372104657552145 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (175 + 1) - 1) % 2 ^ 256 = 2 ^ (175 + 1) - 1 by decide]
  rw [ray_eval_seam_175_lo]
  decide

private theorem wad_eval_seam_175_hi :
    model_ln_wad_to_wad_evm (2 ^ (175 + 1)) = 80547372104657552145 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (175 + 1)) % 2 ^ 256 = 2 ^ (175 + 1) by decide]
  rw [ray_eval_seam_175_hi]
  decide

private theorem ray_seam_175 :
    sle (model_ln_wad_evm (2 ^ (175 + 1) - 1)) (model_ln_wad_evm (2 ^ (175 + 1))) = true := by
  rw [ray_eval_seam_175_lo, ray_eval_seam_175_hi]
  unfold sle
  decide

private theorem wad_seam_175 :
    sle (model_ln_wad_to_wad_evm (2 ^ (175 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (175 + 1))) = true := by
  rw [wad_eval_seam_175_lo, wad_eval_seam_175_hi]
  unfold sle
  decide

private theorem ray_eval_seam_176_lo :
    model_ln_wad_evm (2 ^ (176 + 1) - 1) = 81240519285217497454526239313 := by
  have hlog : Nat.log2 (2 ^ (176 + 1) - 1) = 176 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (176 + 1) - 1) % 2 ^ 256 = 2 ^ (176 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_176_hi :
    model_ln_wad_evm (2 ^ (176 + 1)) = 81240519285217497454526239313 := by
  have hlog : Nat.log2 (2 ^ (176 + 1)) = 177 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (176 + 1)) % 2 ^ 256 = 2 ^ (176 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_176_lo :
    model_ln_wad_to_wad_evm (2 ^ (176 + 1) - 1) = 81240519285217497454 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (176 + 1) - 1) % 2 ^ 256 = 2 ^ (176 + 1) - 1 by decide]
  rw [ray_eval_seam_176_lo]
  decide

private theorem wad_eval_seam_176_hi :
    model_ln_wad_to_wad_evm (2 ^ (176 + 1)) = 81240519285217497454 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (176 + 1)) % 2 ^ 256 = 2 ^ (176 + 1) by decide]
  rw [ray_eval_seam_176_hi]
  decide

private theorem ray_seam_176 :
    sle (model_ln_wad_evm (2 ^ (176 + 1) - 1)) (model_ln_wad_evm (2 ^ (176 + 1))) = true := by
  rw [ray_eval_seam_176_lo, ray_eval_seam_176_hi]
  unfold sle
  decide

private theorem wad_seam_176 :
    sle (model_ln_wad_to_wad_evm (2 ^ (176 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (176 + 1))) = true := by
  rw [wad_eval_seam_176_lo, wad_eval_seam_176_hi]
  unfold sle
  decide

private theorem ray_eval_seam_177_lo :
    model_ln_wad_evm (2 ^ (177 + 1) - 1) = 81933666465777442763943471434 := by
  have hlog : Nat.log2 (2 ^ (177 + 1) - 1) = 177 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (177 + 1) - 1) % 2 ^ 256 = 2 ^ (177 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_177_hi :
    model_ln_wad_evm (2 ^ (177 + 1)) = 81933666465777442763943471435 := by
  have hlog : Nat.log2 (2 ^ (177 + 1)) = 178 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (177 + 1)) % 2 ^ 256 = 2 ^ (177 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_177_lo :
    model_ln_wad_to_wad_evm (2 ^ (177 + 1) - 1) = 81933666465777442763 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (177 + 1) - 1) % 2 ^ 256 = 2 ^ (177 + 1) - 1 by decide]
  rw [ray_eval_seam_177_lo]
  decide

private theorem wad_eval_seam_177_hi :
    model_ln_wad_to_wad_evm (2 ^ (177 + 1)) = 81933666465777442763 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (177 + 1)) % 2 ^ 256 = 2 ^ (177 + 1) by decide]
  rw [ray_eval_seam_177_hi]
  decide

private theorem ray_seam_177 :
    sle (model_ln_wad_evm (2 ^ (177 + 1) - 1)) (model_ln_wad_evm (2 ^ (177 + 1))) = true := by
  rw [ray_eval_seam_177_lo, ray_eval_seam_177_hi]
  unfold sle
  decide

private theorem wad_seam_177 :
    sle (model_ln_wad_to_wad_evm (2 ^ (177 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (177 + 1))) = true := by
  rw [wad_eval_seam_177_lo, wad_eval_seam_177_hi]
  unfold sle
  decide

private theorem ray_eval_seam_178_lo :
    model_ln_wad_evm (2 ^ (178 + 1) - 1) = 82626813646337388073360703556 := by
  have hlog : Nat.log2 (2 ^ (178 + 1) - 1) = 178 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (178 + 1) - 1) % 2 ^ 256 = 2 ^ (178 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_178_hi :
    model_ln_wad_evm (2 ^ (178 + 1)) = 82626813646337388073360703556 := by
  have hlog : Nat.log2 (2 ^ (178 + 1)) = 179 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (178 + 1)) % 2 ^ 256 = 2 ^ (178 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_178_lo :
    model_ln_wad_to_wad_evm (2 ^ (178 + 1) - 1) = 82626813646337388073 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (178 + 1) - 1) % 2 ^ 256 = 2 ^ (178 + 1) - 1 by decide]
  rw [ray_eval_seam_178_lo]
  decide

private theorem wad_eval_seam_178_hi :
    model_ln_wad_to_wad_evm (2 ^ (178 + 1)) = 82626813646337388073 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (178 + 1)) % 2 ^ 256 = 2 ^ (178 + 1) by decide]
  rw [ray_eval_seam_178_hi]
  decide

private theorem ray_seam_178 :
    sle (model_ln_wad_evm (2 ^ (178 + 1) - 1)) (model_ln_wad_evm (2 ^ (178 + 1))) = true := by
  rw [ray_eval_seam_178_lo, ray_eval_seam_178_hi]
  unfold sle
  decide

private theorem wad_seam_178 :
    sle (model_ln_wad_to_wad_evm (2 ^ (178 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (178 + 1))) = true := by
  rw [wad_eval_seam_178_lo, wad_eval_seam_178_hi]
  unfold sle
  decide

private theorem ray_eval_seam_179_lo :
    model_ln_wad_evm (2 ^ (179 + 1) - 1) = 83319960826897333382777935677 := by
  have hlog : Nat.log2 (2 ^ (179 + 1) - 1) = 179 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (179 + 1) - 1) % 2 ^ 256 = 2 ^ (179 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_179_hi :
    model_ln_wad_evm (2 ^ (179 + 1)) = 83319960826897333382777935678 := by
  have hlog : Nat.log2 (2 ^ (179 + 1)) = 180 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (179 + 1)) % 2 ^ 256 = 2 ^ (179 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_179_lo :
    model_ln_wad_to_wad_evm (2 ^ (179 + 1) - 1) = 83319960826897333382 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (179 + 1) - 1) % 2 ^ 256 = 2 ^ (179 + 1) - 1 by decide]
  rw [ray_eval_seam_179_lo]
  decide

private theorem wad_eval_seam_179_hi :
    model_ln_wad_to_wad_evm (2 ^ (179 + 1)) = 83319960826897333382 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (179 + 1)) % 2 ^ 256 = 2 ^ (179 + 1) by decide]
  rw [ray_eval_seam_179_hi]
  decide

private theorem ray_seam_179 :
    sle (model_ln_wad_evm (2 ^ (179 + 1) - 1)) (model_ln_wad_evm (2 ^ (179 + 1))) = true := by
  rw [ray_eval_seam_179_lo, ray_eval_seam_179_hi]
  unfold sle
  decide

private theorem wad_seam_179 :
    sle (model_ln_wad_to_wad_evm (2 ^ (179 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (179 + 1))) = true := by
  rw [wad_eval_seam_179_lo, wad_eval_seam_179_hi]
  unfold sle
  decide

private theorem ray_eval_seam_180_lo :
    model_ln_wad_evm (2 ^ (180 + 1) - 1) = 84013108007457278692195167798 := by
  have hlog : Nat.log2 (2 ^ (180 + 1) - 1) = 180 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (180 + 1) - 1) % 2 ^ 256 = 2 ^ (180 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_180_hi :
    model_ln_wad_evm (2 ^ (180 + 1)) = 84013108007457278692195167799 := by
  have hlog : Nat.log2 (2 ^ (180 + 1)) = 181 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (180 + 1)) % 2 ^ 256 = 2 ^ (180 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_180_lo :
    model_ln_wad_to_wad_evm (2 ^ (180 + 1) - 1) = 84013108007457278692 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (180 + 1) - 1) % 2 ^ 256 = 2 ^ (180 + 1) - 1 by decide]
  rw [ray_eval_seam_180_lo]
  decide

private theorem wad_eval_seam_180_hi :
    model_ln_wad_to_wad_evm (2 ^ (180 + 1)) = 84013108007457278692 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (180 + 1)) % 2 ^ 256 = 2 ^ (180 + 1) by decide]
  rw [ray_eval_seam_180_hi]
  decide

private theorem ray_seam_180 :
    sle (model_ln_wad_evm (2 ^ (180 + 1) - 1)) (model_ln_wad_evm (2 ^ (180 + 1))) = true := by
  rw [ray_eval_seam_180_lo, ray_eval_seam_180_hi]
  unfold sle
  decide

private theorem wad_seam_180 :
    sle (model_ln_wad_to_wad_evm (2 ^ (180 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (180 + 1))) = true := by
  rw [wad_eval_seam_180_lo, wad_eval_seam_180_hi]
  unfold sle
  decide

private theorem ray_eval_seam_181_lo :
    model_ln_wad_evm (2 ^ (181 + 1) - 1) = 84706255188017224001612399920 := by
  have hlog : Nat.log2 (2 ^ (181 + 1) - 1) = 181 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (181 + 1) - 1) % 2 ^ 256 = 2 ^ (181 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_181_hi :
    model_ln_wad_evm (2 ^ (181 + 1)) = 84706255188017224001612399921 := by
  have hlog : Nat.log2 (2 ^ (181 + 1)) = 182 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (181 + 1)) % 2 ^ 256 = 2 ^ (181 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_181_lo :
    model_ln_wad_to_wad_evm (2 ^ (181 + 1) - 1) = 84706255188017224001 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (181 + 1) - 1) % 2 ^ 256 = 2 ^ (181 + 1) - 1 by decide]
  rw [ray_eval_seam_181_lo]
  decide

private theorem wad_eval_seam_181_hi :
    model_ln_wad_to_wad_evm (2 ^ (181 + 1)) = 84706255188017224001 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (181 + 1)) % 2 ^ 256 = 2 ^ (181 + 1) by decide]
  rw [ray_eval_seam_181_hi]
  decide

private theorem ray_seam_181 :
    sle (model_ln_wad_evm (2 ^ (181 + 1) - 1)) (model_ln_wad_evm (2 ^ (181 + 1))) = true := by
  rw [ray_eval_seam_181_lo, ray_eval_seam_181_hi]
  unfold sle
  decide

private theorem wad_seam_181 :
    sle (model_ln_wad_to_wad_evm (2 ^ (181 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (181 + 1))) = true := by
  rw [wad_eval_seam_181_lo, wad_eval_seam_181_hi]
  unfold sle
  decide

private theorem ray_eval_seam_182_lo :
    model_ln_wad_evm (2 ^ (182 + 1) - 1) = 85399402368577169311029632041 := by
  have hlog : Nat.log2 (2 ^ (182 + 1) - 1) = 182 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (182 + 1) - 1) % 2 ^ 256 = 2 ^ (182 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_182_hi :
    model_ln_wad_evm (2 ^ (182 + 1)) = 85399402368577169311029632042 := by
  have hlog : Nat.log2 (2 ^ (182 + 1)) = 183 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (182 + 1)) % 2 ^ 256 = 2 ^ (182 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_182_lo :
    model_ln_wad_to_wad_evm (2 ^ (182 + 1) - 1) = 85399402368577169311 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (182 + 1) - 1) % 2 ^ 256 = 2 ^ (182 + 1) - 1 by decide]
  rw [ray_eval_seam_182_lo]
  decide

private theorem wad_eval_seam_182_hi :
    model_ln_wad_to_wad_evm (2 ^ (182 + 1)) = 85399402368577169311 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (182 + 1)) % 2 ^ 256 = 2 ^ (182 + 1) by decide]
  rw [ray_eval_seam_182_hi]
  decide

private theorem ray_seam_182 :
    sle (model_ln_wad_evm (2 ^ (182 + 1) - 1)) (model_ln_wad_evm (2 ^ (182 + 1))) = true := by
  rw [ray_eval_seam_182_lo, ray_eval_seam_182_hi]
  unfold sle
  decide

private theorem wad_seam_182 :
    sle (model_ln_wad_to_wad_evm (2 ^ (182 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (182 + 1))) = true := by
  rw [wad_eval_seam_182_lo, wad_eval_seam_182_hi]
  unfold sle
  decide

private theorem ray_eval_seam_183_lo :
    model_ln_wad_evm (2 ^ (183 + 1) - 1) = 86092549549137114620446864163 := by
  have hlog : Nat.log2 (2 ^ (183 + 1) - 1) = 183 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (183 + 1) - 1) % 2 ^ 256 = 2 ^ (183 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_183_hi :
    model_ln_wad_evm (2 ^ (183 + 1)) = 86092549549137114620446864163 := by
  have hlog : Nat.log2 (2 ^ (183 + 1)) = 184 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (183 + 1)) % 2 ^ 256 = 2 ^ (183 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_183_lo :
    model_ln_wad_to_wad_evm (2 ^ (183 + 1) - 1) = 86092549549137114620 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (183 + 1) - 1) % 2 ^ 256 = 2 ^ (183 + 1) - 1 by decide]
  rw [ray_eval_seam_183_lo]
  decide

private theorem wad_eval_seam_183_hi :
    model_ln_wad_to_wad_evm (2 ^ (183 + 1)) = 86092549549137114620 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (183 + 1)) % 2 ^ 256 = 2 ^ (183 + 1) by decide]
  rw [ray_eval_seam_183_hi]
  decide

private theorem ray_seam_183 :
    sle (model_ln_wad_evm (2 ^ (183 + 1) - 1)) (model_ln_wad_evm (2 ^ (183 + 1))) = true := by
  rw [ray_eval_seam_183_lo, ray_eval_seam_183_hi]
  unfold sle
  decide

private theorem wad_seam_183 :
    sle (model_ln_wad_to_wad_evm (2 ^ (183 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (183 + 1))) = true := by
  rw [wad_eval_seam_183_lo, wad_eval_seam_183_hi]
  unfold sle
  decide

private theorem ray_eval_seam_184_lo :
    model_ln_wad_evm (2 ^ (184 + 1) - 1) = 86785696729697059929864096284 := by
  have hlog : Nat.log2 (2 ^ (184 + 1) - 1) = 184 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (184 + 1) - 1) % 2 ^ 256 = 2 ^ (184 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_184_hi :
    model_ln_wad_evm (2 ^ (184 + 1)) = 86785696729697059929864096285 := by
  have hlog : Nat.log2 (2 ^ (184 + 1)) = 185 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (184 + 1)) % 2 ^ 256 = 2 ^ (184 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_184_lo :
    model_ln_wad_to_wad_evm (2 ^ (184 + 1) - 1) = 86785696729697059929 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (184 + 1) - 1) % 2 ^ 256 = 2 ^ (184 + 1) - 1 by decide]
  rw [ray_eval_seam_184_lo]
  decide

private theorem wad_eval_seam_184_hi :
    model_ln_wad_to_wad_evm (2 ^ (184 + 1)) = 86785696729697059929 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (184 + 1)) % 2 ^ 256 = 2 ^ (184 + 1) by decide]
  rw [ray_eval_seam_184_hi]
  decide

private theorem ray_seam_184 :
    sle (model_ln_wad_evm (2 ^ (184 + 1) - 1)) (model_ln_wad_evm (2 ^ (184 + 1))) = true := by
  rw [ray_eval_seam_184_lo, ray_eval_seam_184_hi]
  unfold sle
  decide

private theorem wad_seam_184 :
    sle (model_ln_wad_to_wad_evm (2 ^ (184 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (184 + 1))) = true := by
  rw [wad_eval_seam_184_lo, wad_eval_seam_184_hi]
  unfold sle
  decide

private theorem ray_eval_seam_185_lo :
    model_ln_wad_evm (2 ^ (185 + 1) - 1) = 87478843910257005239281328406 := by
  have hlog : Nat.log2 (2 ^ (185 + 1) - 1) = 185 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (185 + 1) - 1) % 2 ^ 256 = 2 ^ (185 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_185_hi :
    model_ln_wad_evm (2 ^ (185 + 1)) = 87478843910257005239281328406 := by
  have hlog : Nat.log2 (2 ^ (185 + 1)) = 186 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (185 + 1)) % 2 ^ 256 = 2 ^ (185 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_185_lo :
    model_ln_wad_to_wad_evm (2 ^ (185 + 1) - 1) = 87478843910257005239 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (185 + 1) - 1) % 2 ^ 256 = 2 ^ (185 + 1) - 1 by decide]
  rw [ray_eval_seam_185_lo]
  decide

private theorem wad_eval_seam_185_hi :
    model_ln_wad_to_wad_evm (2 ^ (185 + 1)) = 87478843910257005239 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (185 + 1)) % 2 ^ 256 = 2 ^ (185 + 1) by decide]
  rw [ray_eval_seam_185_hi]
  decide

private theorem ray_seam_185 :
    sle (model_ln_wad_evm (2 ^ (185 + 1) - 1)) (model_ln_wad_evm (2 ^ (185 + 1))) = true := by
  rw [ray_eval_seam_185_lo, ray_eval_seam_185_hi]
  unfold sle
  decide

private theorem wad_seam_185 :
    sle (model_ln_wad_to_wad_evm (2 ^ (185 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (185 + 1))) = true := by
  rw [wad_eval_seam_185_lo, wad_eval_seam_185_hi]
  unfold sle
  decide

private theorem ray_eval_seam_186_lo :
    model_ln_wad_evm (2 ^ (186 + 1) - 1) = 88171991090816950548698560527 := by
  have hlog : Nat.log2 (2 ^ (186 + 1) - 1) = 186 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (186 + 1) - 1) % 2 ^ 256 = 2 ^ (186 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_186_hi :
    model_ln_wad_evm (2 ^ (186 + 1)) = 88171991090816950548698560528 := by
  have hlog : Nat.log2 (2 ^ (186 + 1)) = 187 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (186 + 1)) % 2 ^ 256 = 2 ^ (186 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_186_lo :
    model_ln_wad_to_wad_evm (2 ^ (186 + 1) - 1) = 88171991090816950548 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (186 + 1) - 1) % 2 ^ 256 = 2 ^ (186 + 1) - 1 by decide]
  rw [ray_eval_seam_186_lo]
  decide

private theorem wad_eval_seam_186_hi :
    model_ln_wad_to_wad_evm (2 ^ (186 + 1)) = 88171991090816950548 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (186 + 1)) % 2 ^ 256 = 2 ^ (186 + 1) by decide]
  rw [ray_eval_seam_186_hi]
  decide

private theorem ray_seam_186 :
    sle (model_ln_wad_evm (2 ^ (186 + 1) - 1)) (model_ln_wad_evm (2 ^ (186 + 1))) = true := by
  rw [ray_eval_seam_186_lo, ray_eval_seam_186_hi]
  unfold sle
  decide

private theorem wad_seam_186 :
    sle (model_ln_wad_to_wad_evm (2 ^ (186 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (186 + 1))) = true := by
  rw [wad_eval_seam_186_lo, wad_eval_seam_186_hi]
  unfold sle
  decide

private theorem ray_eval_seam_187_lo :
    model_ln_wad_evm (2 ^ (187 + 1) - 1) = 88865138271376895858115792649 := by
  have hlog : Nat.log2 (2 ^ (187 + 1) - 1) = 187 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (187 + 1) - 1) % 2 ^ 256 = 2 ^ (187 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_187_hi :
    model_ln_wad_evm (2 ^ (187 + 1)) = 88865138271376895858115792649 := by
  have hlog : Nat.log2 (2 ^ (187 + 1)) = 188 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (187 + 1)) % 2 ^ 256 = 2 ^ (187 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_187_lo :
    model_ln_wad_to_wad_evm (2 ^ (187 + 1) - 1) = 88865138271376895858 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (187 + 1) - 1) % 2 ^ 256 = 2 ^ (187 + 1) - 1 by decide]
  rw [ray_eval_seam_187_lo]
  decide

private theorem wad_eval_seam_187_hi :
    model_ln_wad_to_wad_evm (2 ^ (187 + 1)) = 88865138271376895858 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (187 + 1)) % 2 ^ 256 = 2 ^ (187 + 1) by decide]
  rw [ray_eval_seam_187_hi]
  decide

private theorem ray_seam_187 :
    sle (model_ln_wad_evm (2 ^ (187 + 1) - 1)) (model_ln_wad_evm (2 ^ (187 + 1))) = true := by
  rw [ray_eval_seam_187_lo, ray_eval_seam_187_hi]
  unfold sle
  decide

private theorem wad_seam_187 :
    sle (model_ln_wad_to_wad_evm (2 ^ (187 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (187 + 1))) = true := by
  rw [wad_eval_seam_187_lo, wad_eval_seam_187_hi]
  unfold sle
  decide

private theorem ray_eval_seam_188_lo :
    model_ln_wad_evm (2 ^ (188 + 1) - 1) = 89558285451936841167533024770 := by
  have hlog : Nat.log2 (2 ^ (188 + 1) - 1) = 188 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (188 + 1) - 1) % 2 ^ 256 = 2 ^ (188 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_188_hi :
    model_ln_wad_evm (2 ^ (188 + 1)) = 89558285451936841167533024771 := by
  have hlog : Nat.log2 (2 ^ (188 + 1)) = 189 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (188 + 1)) % 2 ^ 256 = 2 ^ (188 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_188_lo :
    model_ln_wad_to_wad_evm (2 ^ (188 + 1) - 1) = 89558285451936841167 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (188 + 1) - 1) % 2 ^ 256 = 2 ^ (188 + 1) - 1 by decide]
  rw [ray_eval_seam_188_lo]
  decide

private theorem wad_eval_seam_188_hi :
    model_ln_wad_to_wad_evm (2 ^ (188 + 1)) = 89558285451936841167 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (188 + 1)) % 2 ^ 256 = 2 ^ (188 + 1) by decide]
  rw [ray_eval_seam_188_hi]
  decide

private theorem ray_seam_188 :
    sle (model_ln_wad_evm (2 ^ (188 + 1) - 1)) (model_ln_wad_evm (2 ^ (188 + 1))) = true := by
  rw [ray_eval_seam_188_lo, ray_eval_seam_188_hi]
  unfold sle
  decide

private theorem wad_seam_188 :
    sle (model_ln_wad_to_wad_evm (2 ^ (188 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (188 + 1))) = true := by
  rw [wad_eval_seam_188_lo, wad_eval_seam_188_hi]
  unfold sle
  decide

private theorem ray_eval_seam_189_lo :
    model_ln_wad_evm (2 ^ (189 + 1) - 1) = 90251432632496786476950256892 := by
  have hlog : Nat.log2 (2 ^ (189 + 1) - 1) = 189 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (189 + 1) - 1) % 2 ^ 256 = 2 ^ (189 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_189_hi :
    model_ln_wad_evm (2 ^ (189 + 1)) = 90251432632496786476950256892 := by
  have hlog : Nat.log2 (2 ^ (189 + 1)) = 190 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (189 + 1)) % 2 ^ 256 = 2 ^ (189 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_189_lo :
    model_ln_wad_to_wad_evm (2 ^ (189 + 1) - 1) = 90251432632496786476 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (189 + 1) - 1) % 2 ^ 256 = 2 ^ (189 + 1) - 1 by decide]
  rw [ray_eval_seam_189_lo]
  decide

private theorem wad_eval_seam_189_hi :
    model_ln_wad_to_wad_evm (2 ^ (189 + 1)) = 90251432632496786476 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (189 + 1)) % 2 ^ 256 = 2 ^ (189 + 1) by decide]
  rw [ray_eval_seam_189_hi]
  decide

private theorem ray_seam_189 :
    sle (model_ln_wad_evm (2 ^ (189 + 1) - 1)) (model_ln_wad_evm (2 ^ (189 + 1))) = true := by
  rw [ray_eval_seam_189_lo, ray_eval_seam_189_hi]
  unfold sle
  decide

private theorem wad_seam_189 :
    sle (model_ln_wad_to_wad_evm (2 ^ (189 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (189 + 1))) = true := by
  rw [wad_eval_seam_189_lo, wad_eval_seam_189_hi]
  unfold sle
  decide

private theorem ray_eval_seam_190_lo :
    model_ln_wad_evm (2 ^ (190 + 1) - 1) = 90944579813056731786367489013 := by
  have hlog : Nat.log2 (2 ^ (190 + 1) - 1) = 190 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (190 + 1) - 1) % 2 ^ 256 = 2 ^ (190 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_190_hi :
    model_ln_wad_evm (2 ^ (190 + 1)) = 90944579813056731786367489014 := by
  have hlog : Nat.log2 (2 ^ (190 + 1)) = 191 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (190 + 1)) % 2 ^ 256 = 2 ^ (190 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_190_lo :
    model_ln_wad_to_wad_evm (2 ^ (190 + 1) - 1) = 90944579813056731786 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (190 + 1) - 1) % 2 ^ 256 = 2 ^ (190 + 1) - 1 by decide]
  rw [ray_eval_seam_190_lo]
  decide

private theorem wad_eval_seam_190_hi :
    model_ln_wad_to_wad_evm (2 ^ (190 + 1)) = 90944579813056731786 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (190 + 1)) % 2 ^ 256 = 2 ^ (190 + 1) by decide]
  rw [ray_eval_seam_190_hi]
  decide

private theorem ray_seam_190 :
    sle (model_ln_wad_evm (2 ^ (190 + 1) - 1)) (model_ln_wad_evm (2 ^ (190 + 1))) = true := by
  rw [ray_eval_seam_190_lo, ray_eval_seam_190_hi]
  unfold sle
  decide

private theorem wad_seam_190 :
    sle (model_ln_wad_to_wad_evm (2 ^ (190 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (190 + 1))) = true := by
  rw [wad_eval_seam_190_lo, wad_eval_seam_190_hi]
  unfold sle
  decide

private theorem ray_eval_seam_191_lo :
    model_ln_wad_evm (2 ^ (191 + 1) - 1) = 91637726993616677095784721134 := by
  have hlog : Nat.log2 (2 ^ (191 + 1) - 1) = 191 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (191 + 1) - 1) % 2 ^ 256 = 2 ^ (191 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_191_hi :
    model_ln_wad_evm (2 ^ (191 + 1)) = 91637726993616677095784721135 := by
  have hlog : Nat.log2 (2 ^ (191 + 1)) = 192 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (191 + 1)) % 2 ^ 256 = 2 ^ (191 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_191_lo :
    model_ln_wad_to_wad_evm (2 ^ (191 + 1) - 1) = 91637726993616677095 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (191 + 1) - 1) % 2 ^ 256 = 2 ^ (191 + 1) - 1 by decide]
  rw [ray_eval_seam_191_lo]
  decide

private theorem wad_eval_seam_191_hi :
    model_ln_wad_to_wad_evm (2 ^ (191 + 1)) = 91637726993616677095 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (191 + 1)) % 2 ^ 256 = 2 ^ (191 + 1) by decide]
  rw [ray_eval_seam_191_hi]
  decide

private theorem ray_seam_191 :
    sle (model_ln_wad_evm (2 ^ (191 + 1) - 1)) (model_ln_wad_evm (2 ^ (191 + 1))) = true := by
  rw [ray_eval_seam_191_lo, ray_eval_seam_191_hi]
  unfold sle
  decide

private theorem wad_seam_191 :
    sle (model_ln_wad_to_wad_evm (2 ^ (191 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (191 + 1))) = true := by
  rw [wad_eval_seam_191_lo, wad_eval_seam_191_hi]
  unfold sle
  decide

private theorem ray_eval_seam_192_lo :
    model_ln_wad_evm (2 ^ (192 + 1) - 1) = 92330874174176622405201953256 := by
  have hlog : Nat.log2 (2 ^ (192 + 1) - 1) = 192 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (192 + 1) - 1) % 2 ^ 256 = 2 ^ (192 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_192_hi :
    model_ln_wad_evm (2 ^ (192 + 1)) = 92330874174176622405201953257 := by
  have hlog : Nat.log2 (2 ^ (192 + 1)) = 193 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (192 + 1)) % 2 ^ 256 = 2 ^ (192 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_192_lo :
    model_ln_wad_to_wad_evm (2 ^ (192 + 1) - 1) = 92330874174176622405 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (192 + 1) - 1) % 2 ^ 256 = 2 ^ (192 + 1) - 1 by decide]
  rw [ray_eval_seam_192_lo]
  decide

private theorem wad_eval_seam_192_hi :
    model_ln_wad_to_wad_evm (2 ^ (192 + 1)) = 92330874174176622405 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (192 + 1)) % 2 ^ 256 = 2 ^ (192 + 1) by decide]
  rw [ray_eval_seam_192_hi]
  decide

private theorem ray_seam_192 :
    sle (model_ln_wad_evm (2 ^ (192 + 1) - 1)) (model_ln_wad_evm (2 ^ (192 + 1))) = true := by
  rw [ray_eval_seam_192_lo, ray_eval_seam_192_hi]
  unfold sle
  decide

private theorem wad_seam_192 :
    sle (model_ln_wad_to_wad_evm (2 ^ (192 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (192 + 1))) = true := by
  rw [wad_eval_seam_192_lo, wad_eval_seam_192_hi]
  unfold sle
  decide

private theorem ray_eval_seam_193_lo :
    model_ln_wad_evm (2 ^ (193 + 1) - 1) = 93024021354736567714619185377 := by
  have hlog : Nat.log2 (2 ^ (193 + 1) - 1) = 193 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (193 + 1) - 1) % 2 ^ 256 = 2 ^ (193 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_193_hi :
    model_ln_wad_evm (2 ^ (193 + 1)) = 93024021354736567714619185378 := by
  have hlog : Nat.log2 (2 ^ (193 + 1)) = 194 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (193 + 1)) % 2 ^ 256 = 2 ^ (193 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_193_lo :
    model_ln_wad_to_wad_evm (2 ^ (193 + 1) - 1) = 93024021354736567714 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (193 + 1) - 1) % 2 ^ 256 = 2 ^ (193 + 1) - 1 by decide]
  rw [ray_eval_seam_193_lo]
  decide

private theorem wad_eval_seam_193_hi :
    model_ln_wad_to_wad_evm (2 ^ (193 + 1)) = 93024021354736567714 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (193 + 1)) % 2 ^ 256 = 2 ^ (193 + 1) by decide]
  rw [ray_eval_seam_193_hi]
  decide

private theorem ray_seam_193 :
    sle (model_ln_wad_evm (2 ^ (193 + 1) - 1)) (model_ln_wad_evm (2 ^ (193 + 1))) = true := by
  rw [ray_eval_seam_193_lo, ray_eval_seam_193_hi]
  unfold sle
  decide

private theorem wad_seam_193 :
    sle (model_ln_wad_to_wad_evm (2 ^ (193 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (193 + 1))) = true := by
  rw [wad_eval_seam_193_lo, wad_eval_seam_193_hi]
  unfold sle
  decide

private theorem ray_eval_seam_194_lo :
    model_ln_wad_evm (2 ^ (194 + 1) - 1) = 93717168535296513024036417499 := by
  have hlog : Nat.log2 (2 ^ (194 + 1) - 1) = 194 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (194 + 1) - 1) % 2 ^ 256 = 2 ^ (194 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_194_hi :
    model_ln_wad_evm (2 ^ (194 + 1)) = 93717168535296513024036417500 := by
  have hlog : Nat.log2 (2 ^ (194 + 1)) = 195 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (194 + 1)) % 2 ^ 256 = 2 ^ (194 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_194_lo :
    model_ln_wad_to_wad_evm (2 ^ (194 + 1) - 1) = 93717168535296513024 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (194 + 1) - 1) % 2 ^ 256 = 2 ^ (194 + 1) - 1 by decide]
  rw [ray_eval_seam_194_lo]
  decide

private theorem wad_eval_seam_194_hi :
    model_ln_wad_to_wad_evm (2 ^ (194 + 1)) = 93717168535296513024 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (194 + 1)) % 2 ^ 256 = 2 ^ (194 + 1) by decide]
  rw [ray_eval_seam_194_hi]
  decide

private theorem ray_seam_194 :
    sle (model_ln_wad_evm (2 ^ (194 + 1) - 1)) (model_ln_wad_evm (2 ^ (194 + 1))) = true := by
  rw [ray_eval_seam_194_lo, ray_eval_seam_194_hi]
  unfold sle
  decide

private theorem wad_seam_194 :
    sle (model_ln_wad_to_wad_evm (2 ^ (194 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (194 + 1))) = true := by
  rw [wad_eval_seam_194_lo, wad_eval_seam_194_hi]
  unfold sle
  decide

private theorem ray_eval_seam_195_lo :
    model_ln_wad_evm (2 ^ (195 + 1) - 1) = 94410315715856458333453649620 := by
  have hlog : Nat.log2 (2 ^ (195 + 1) - 1) = 195 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (195 + 1) - 1) % 2 ^ 256 = 2 ^ (195 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_195_hi :
    model_ln_wad_evm (2 ^ (195 + 1)) = 94410315715856458333453649621 := by
  have hlog : Nat.log2 (2 ^ (195 + 1)) = 196 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (195 + 1)) % 2 ^ 256 = 2 ^ (195 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_195_lo :
    model_ln_wad_to_wad_evm (2 ^ (195 + 1) - 1) = 94410315715856458333 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (195 + 1) - 1) % 2 ^ 256 = 2 ^ (195 + 1) - 1 by decide]
  rw [ray_eval_seam_195_lo]
  decide

private theorem wad_eval_seam_195_hi :
    model_ln_wad_to_wad_evm (2 ^ (195 + 1)) = 94410315715856458333 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (195 + 1)) % 2 ^ 256 = 2 ^ (195 + 1) by decide]
  rw [ray_eval_seam_195_hi]
  decide

private theorem ray_seam_195 :
    sle (model_ln_wad_evm (2 ^ (195 + 1) - 1)) (model_ln_wad_evm (2 ^ (195 + 1))) = true := by
  rw [ray_eval_seam_195_lo, ray_eval_seam_195_hi]
  unfold sle
  decide

private theorem wad_seam_195 :
    sle (model_ln_wad_to_wad_evm (2 ^ (195 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (195 + 1))) = true := by
  rw [wad_eval_seam_195_lo, wad_eval_seam_195_hi]
  unfold sle
  decide

private theorem ray_eval_seam_196_lo :
    model_ln_wad_evm (2 ^ (196 + 1) - 1) = 95103462896416403642870881742 := by
  have hlog : Nat.log2 (2 ^ (196 + 1) - 1) = 196 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (196 + 1) - 1) % 2 ^ 256 = 2 ^ (196 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_196_hi :
    model_ln_wad_evm (2 ^ (196 + 1)) = 95103462896416403642870881742 := by
  have hlog : Nat.log2 (2 ^ (196 + 1)) = 197 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (196 + 1)) % 2 ^ 256 = 2 ^ (196 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_196_lo :
    model_ln_wad_to_wad_evm (2 ^ (196 + 1) - 1) = 95103462896416403642 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (196 + 1) - 1) % 2 ^ 256 = 2 ^ (196 + 1) - 1 by decide]
  rw [ray_eval_seam_196_lo]
  decide

private theorem wad_eval_seam_196_hi :
    model_ln_wad_to_wad_evm (2 ^ (196 + 1)) = 95103462896416403642 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (196 + 1)) % 2 ^ 256 = 2 ^ (196 + 1) by decide]
  rw [ray_eval_seam_196_hi]
  decide

private theorem ray_seam_196 :
    sle (model_ln_wad_evm (2 ^ (196 + 1) - 1)) (model_ln_wad_evm (2 ^ (196 + 1))) = true := by
  rw [ray_eval_seam_196_lo, ray_eval_seam_196_hi]
  unfold sle
  decide

private theorem wad_seam_196 :
    sle (model_ln_wad_to_wad_evm (2 ^ (196 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (196 + 1))) = true := by
  rw [wad_eval_seam_196_lo, wad_eval_seam_196_hi]
  unfold sle
  decide

private theorem ray_eval_seam_197_lo :
    model_ln_wad_evm (2 ^ (197 + 1) - 1) = 95796610076976348952288113863 := by
  have hlog : Nat.log2 (2 ^ (197 + 1) - 1) = 197 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (197 + 1) - 1) % 2 ^ 256 = 2 ^ (197 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_197_hi :
    model_ln_wad_evm (2 ^ (197 + 1)) = 95796610076976348952288113864 := by
  have hlog : Nat.log2 (2 ^ (197 + 1)) = 198 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (197 + 1)) % 2 ^ 256 = 2 ^ (197 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_197_lo :
    model_ln_wad_to_wad_evm (2 ^ (197 + 1) - 1) = 95796610076976348952 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (197 + 1) - 1) % 2 ^ 256 = 2 ^ (197 + 1) - 1 by decide]
  rw [ray_eval_seam_197_lo]
  decide

private theorem wad_eval_seam_197_hi :
    model_ln_wad_to_wad_evm (2 ^ (197 + 1)) = 95796610076976348952 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (197 + 1)) % 2 ^ 256 = 2 ^ (197 + 1) by decide]
  rw [ray_eval_seam_197_hi]
  decide

private theorem ray_seam_197 :
    sle (model_ln_wad_evm (2 ^ (197 + 1) - 1)) (model_ln_wad_evm (2 ^ (197 + 1))) = true := by
  rw [ray_eval_seam_197_lo, ray_eval_seam_197_hi]
  unfold sle
  decide

private theorem wad_seam_197 :
    sle (model_ln_wad_to_wad_evm (2 ^ (197 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (197 + 1))) = true := by
  rw [wad_eval_seam_197_lo, wad_eval_seam_197_hi]
  unfold sle
  decide

private theorem ray_eval_seam_198_lo :
    model_ln_wad_evm (2 ^ (198 + 1) - 1) = 96489757257536294261705345985 := by
  have hlog : Nat.log2 (2 ^ (198 + 1) - 1) = 198 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (198 + 1) - 1) % 2 ^ 256 = 2 ^ (198 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_198_hi :
    model_ln_wad_evm (2 ^ (198 + 1)) = 96489757257536294261705345985 := by
  have hlog : Nat.log2 (2 ^ (198 + 1)) = 199 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (198 + 1)) % 2 ^ 256 = 2 ^ (198 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_198_lo :
    model_ln_wad_to_wad_evm (2 ^ (198 + 1) - 1) = 96489757257536294261 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (198 + 1) - 1) % 2 ^ 256 = 2 ^ (198 + 1) - 1 by decide]
  rw [ray_eval_seam_198_lo]
  decide

private theorem wad_eval_seam_198_hi :
    model_ln_wad_to_wad_evm (2 ^ (198 + 1)) = 96489757257536294261 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (198 + 1)) % 2 ^ 256 = 2 ^ (198 + 1) by decide]
  rw [ray_eval_seam_198_hi]
  decide

private theorem ray_seam_198 :
    sle (model_ln_wad_evm (2 ^ (198 + 1) - 1)) (model_ln_wad_evm (2 ^ (198 + 1))) = true := by
  rw [ray_eval_seam_198_lo, ray_eval_seam_198_hi]
  unfold sle
  decide

private theorem wad_seam_198 :
    sle (model_ln_wad_to_wad_evm (2 ^ (198 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (198 + 1))) = true := by
  rw [wad_eval_seam_198_lo, wad_eval_seam_198_hi]
  unfold sle
  decide

private theorem ray_eval_seam_199_lo :
    model_ln_wad_evm (2 ^ (199 + 1) - 1) = 97182904438096239571122578106 := by
  have hlog : Nat.log2 (2 ^ (199 + 1) - 1) = 199 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (199 + 1) - 1) % 2 ^ 256 = 2 ^ (199 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_199_hi :
    model_ln_wad_evm (2 ^ (199 + 1)) = 97182904438096239571122578107 := by
  have hlog : Nat.log2 (2 ^ (199 + 1)) = 200 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (199 + 1)) % 2 ^ 256 = 2 ^ (199 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_199_lo :
    model_ln_wad_to_wad_evm (2 ^ (199 + 1) - 1) = 97182904438096239571 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (199 + 1) - 1) % 2 ^ 256 = 2 ^ (199 + 1) - 1 by decide]
  rw [ray_eval_seam_199_lo]
  decide

private theorem wad_eval_seam_199_hi :
    model_ln_wad_to_wad_evm (2 ^ (199 + 1)) = 97182904438096239571 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (199 + 1)) % 2 ^ 256 = 2 ^ (199 + 1) by decide]
  rw [ray_eval_seam_199_hi]
  decide

private theorem ray_seam_199 :
    sle (model_ln_wad_evm (2 ^ (199 + 1) - 1)) (model_ln_wad_evm (2 ^ (199 + 1))) = true := by
  rw [ray_eval_seam_199_lo, ray_eval_seam_199_hi]
  unfold sle
  decide

private theorem wad_seam_199 :
    sle (model_ln_wad_to_wad_evm (2 ^ (199 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (199 + 1))) = true := by
  rw [wad_eval_seam_199_lo, wad_eval_seam_199_hi]
  unfold sle
  decide

private theorem ray_eval_seam_200_lo :
    model_ln_wad_evm (2 ^ (200 + 1) - 1) = 97876051618656184880539810228 := by
  have hlog : Nat.log2 (2 ^ (200 + 1) - 1) = 200 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (200 + 1) - 1) % 2 ^ 256 = 2 ^ (200 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_200_hi :
    model_ln_wad_evm (2 ^ (200 + 1)) = 97876051618656184880539810228 := by
  have hlog : Nat.log2 (2 ^ (200 + 1)) = 201 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (200 + 1)) % 2 ^ 256 = 2 ^ (200 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_200_lo :
    model_ln_wad_to_wad_evm (2 ^ (200 + 1) - 1) = 97876051618656184880 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (200 + 1) - 1) % 2 ^ 256 = 2 ^ (200 + 1) - 1 by decide]
  rw [ray_eval_seam_200_lo]
  decide

private theorem wad_eval_seam_200_hi :
    model_ln_wad_to_wad_evm (2 ^ (200 + 1)) = 97876051618656184880 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (200 + 1)) % 2 ^ 256 = 2 ^ (200 + 1) by decide]
  rw [ray_eval_seam_200_hi]
  decide

private theorem ray_seam_200 :
    sle (model_ln_wad_evm (2 ^ (200 + 1) - 1)) (model_ln_wad_evm (2 ^ (200 + 1))) = true := by
  rw [ray_eval_seam_200_lo, ray_eval_seam_200_hi]
  unfold sle
  decide

private theorem wad_seam_200 :
    sle (model_ln_wad_to_wad_evm (2 ^ (200 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (200 + 1))) = true := by
  rw [wad_eval_seam_200_lo, wad_eval_seam_200_hi]
  unfold sle
  decide

private theorem ray_eval_seam_201_lo :
    model_ln_wad_evm (2 ^ (201 + 1) - 1) = 98569198799216130189957042349 := by
  have hlog : Nat.log2 (2 ^ (201 + 1) - 1) = 201 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (201 + 1) - 1) % 2 ^ 256 = 2 ^ (201 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_201_hi :
    model_ln_wad_evm (2 ^ (201 + 1)) = 98569198799216130189957042350 := by
  have hlog : Nat.log2 (2 ^ (201 + 1)) = 202 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (201 + 1)) % 2 ^ 256 = 2 ^ (201 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_201_lo :
    model_ln_wad_to_wad_evm (2 ^ (201 + 1) - 1) = 98569198799216130189 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (201 + 1) - 1) % 2 ^ 256 = 2 ^ (201 + 1) - 1 by decide]
  rw [ray_eval_seam_201_lo]
  decide

private theorem wad_eval_seam_201_hi :
    model_ln_wad_to_wad_evm (2 ^ (201 + 1)) = 98569198799216130189 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (201 + 1)) % 2 ^ 256 = 2 ^ (201 + 1) by decide]
  rw [ray_eval_seam_201_hi]
  decide

private theorem ray_seam_201 :
    sle (model_ln_wad_evm (2 ^ (201 + 1) - 1)) (model_ln_wad_evm (2 ^ (201 + 1))) = true := by
  rw [ray_eval_seam_201_lo, ray_eval_seam_201_hi]
  unfold sle
  decide

private theorem wad_seam_201 :
    sle (model_ln_wad_to_wad_evm (2 ^ (201 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (201 + 1))) = true := by
  rw [wad_eval_seam_201_lo, wad_eval_seam_201_hi]
  unfold sle
  decide

private theorem ray_eval_seam_202_lo :
    model_ln_wad_evm (2 ^ (202 + 1) - 1) = 99262345979776075499374274471 := by
  have hlog : Nat.log2 (2 ^ (202 + 1) - 1) = 202 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (202 + 1) - 1) % 2 ^ 256 = 2 ^ (202 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_202_hi :
    model_ln_wad_evm (2 ^ (202 + 1)) = 99262345979776075499374274471 := by
  have hlog : Nat.log2 (2 ^ (202 + 1)) = 203 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (202 + 1)) % 2 ^ 256 = 2 ^ (202 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_202_lo :
    model_ln_wad_to_wad_evm (2 ^ (202 + 1) - 1) = 99262345979776075499 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (202 + 1) - 1) % 2 ^ 256 = 2 ^ (202 + 1) - 1 by decide]
  rw [ray_eval_seam_202_lo]
  decide

private theorem wad_eval_seam_202_hi :
    model_ln_wad_to_wad_evm (2 ^ (202 + 1)) = 99262345979776075499 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (202 + 1)) % 2 ^ 256 = 2 ^ (202 + 1) by decide]
  rw [ray_eval_seam_202_hi]
  decide

private theorem ray_seam_202 :
    sle (model_ln_wad_evm (2 ^ (202 + 1) - 1)) (model_ln_wad_evm (2 ^ (202 + 1))) = true := by
  rw [ray_eval_seam_202_lo, ray_eval_seam_202_hi]
  unfold sle
  decide

private theorem wad_seam_202 :
    sle (model_ln_wad_to_wad_evm (2 ^ (202 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (202 + 1))) = true := by
  rw [wad_eval_seam_202_lo, wad_eval_seam_202_hi]
  unfold sle
  decide

private theorem ray_eval_seam_203_lo :
    model_ln_wad_evm (2 ^ (203 + 1) - 1) = 99955493160336020808791506592 := by
  have hlog : Nat.log2 (2 ^ (203 + 1) - 1) = 203 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (203 + 1) - 1) % 2 ^ 256 = 2 ^ (203 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_203_hi :
    model_ln_wad_evm (2 ^ (203 + 1)) = 99955493160336020808791506593 := by
  have hlog : Nat.log2 (2 ^ (203 + 1)) = 204 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (203 + 1)) % 2 ^ 256 = 2 ^ (203 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_203_lo :
    model_ln_wad_to_wad_evm (2 ^ (203 + 1) - 1) = 99955493160336020808 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (203 + 1) - 1) % 2 ^ 256 = 2 ^ (203 + 1) - 1 by decide]
  rw [ray_eval_seam_203_lo]
  decide

private theorem wad_eval_seam_203_hi :
    model_ln_wad_to_wad_evm (2 ^ (203 + 1)) = 99955493160336020808 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (203 + 1)) % 2 ^ 256 = 2 ^ (203 + 1) by decide]
  rw [ray_eval_seam_203_hi]
  decide

private theorem ray_seam_203 :
    sle (model_ln_wad_evm (2 ^ (203 + 1) - 1)) (model_ln_wad_evm (2 ^ (203 + 1))) = true := by
  rw [ray_eval_seam_203_lo, ray_eval_seam_203_hi]
  unfold sle
  decide

private theorem wad_seam_203 :
    sle (model_ln_wad_to_wad_evm (2 ^ (203 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (203 + 1))) = true := by
  rw [wad_eval_seam_203_lo, wad_eval_seam_203_hi]
  unfold sle
  decide

private theorem ray_eval_seam_204_lo :
    model_ln_wad_evm (2 ^ (204 + 1) - 1) = 100648640340895966118208738713 := by
  have hlog : Nat.log2 (2 ^ (204 + 1) - 1) = 204 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (204 + 1) - 1) % 2 ^ 256 = 2 ^ (204 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_204_hi :
    model_ln_wad_evm (2 ^ (204 + 1)) = 100648640340895966118208738714 := by
  have hlog : Nat.log2 (2 ^ (204 + 1)) = 205 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (204 + 1)) % 2 ^ 256 = 2 ^ (204 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_204_lo :
    model_ln_wad_to_wad_evm (2 ^ (204 + 1) - 1) = 100648640340895966118 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (204 + 1) - 1) % 2 ^ 256 = 2 ^ (204 + 1) - 1 by decide]
  rw [ray_eval_seam_204_lo]
  decide

private theorem wad_eval_seam_204_hi :
    model_ln_wad_to_wad_evm (2 ^ (204 + 1)) = 100648640340895966118 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (204 + 1)) % 2 ^ 256 = 2 ^ (204 + 1) by decide]
  rw [ray_eval_seam_204_hi]
  decide

private theorem ray_seam_204 :
    sle (model_ln_wad_evm (2 ^ (204 + 1) - 1)) (model_ln_wad_evm (2 ^ (204 + 1))) = true := by
  rw [ray_eval_seam_204_lo, ray_eval_seam_204_hi]
  unfold sle
  decide

private theorem wad_seam_204 :
    sle (model_ln_wad_to_wad_evm (2 ^ (204 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (204 + 1))) = true := by
  rw [wad_eval_seam_204_lo, wad_eval_seam_204_hi]
  unfold sle
  decide

private theorem ray_eval_seam_205_lo :
    model_ln_wad_evm (2 ^ (205 + 1) - 1) = 101341787521455911427625970835 := by
  have hlog : Nat.log2 (2 ^ (205 + 1) - 1) = 205 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (205 + 1) - 1) % 2 ^ 256 = 2 ^ (205 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_205_hi :
    model_ln_wad_evm (2 ^ (205 + 1)) = 101341787521455911427625970836 := by
  have hlog : Nat.log2 (2 ^ (205 + 1)) = 206 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (205 + 1)) % 2 ^ 256 = 2 ^ (205 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_205_lo :
    model_ln_wad_to_wad_evm (2 ^ (205 + 1) - 1) = 101341787521455911427 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (205 + 1) - 1) % 2 ^ 256 = 2 ^ (205 + 1) - 1 by decide]
  rw [ray_eval_seam_205_lo]
  decide

private theorem wad_eval_seam_205_hi :
    model_ln_wad_to_wad_evm (2 ^ (205 + 1)) = 101341787521455911427 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (205 + 1)) % 2 ^ 256 = 2 ^ (205 + 1) by decide]
  rw [ray_eval_seam_205_hi]
  decide

private theorem ray_seam_205 :
    sle (model_ln_wad_evm (2 ^ (205 + 1) - 1)) (model_ln_wad_evm (2 ^ (205 + 1))) = true := by
  rw [ray_eval_seam_205_lo, ray_eval_seam_205_hi]
  unfold sle
  decide

private theorem wad_seam_205 :
    sle (model_ln_wad_to_wad_evm (2 ^ (205 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (205 + 1))) = true := by
  rw [wad_eval_seam_205_lo, wad_eval_seam_205_hi]
  unfold sle
  decide

private theorem ray_eval_seam_206_lo :
    model_ln_wad_evm (2 ^ (206 + 1) - 1) = 102034934702015856737043202956 := by
  have hlog : Nat.log2 (2 ^ (206 + 1) - 1) = 206 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (206 + 1) - 1) % 2 ^ 256 = 2 ^ (206 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_206_hi :
    model_ln_wad_evm (2 ^ (206 + 1)) = 102034934702015856737043202957 := by
  have hlog : Nat.log2 (2 ^ (206 + 1)) = 207 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (206 + 1)) % 2 ^ 256 = 2 ^ (206 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_206_lo :
    model_ln_wad_to_wad_evm (2 ^ (206 + 1) - 1) = 102034934702015856737 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (206 + 1) - 1) % 2 ^ 256 = 2 ^ (206 + 1) - 1 by decide]
  rw [ray_eval_seam_206_lo]
  decide

private theorem wad_eval_seam_206_hi :
    model_ln_wad_to_wad_evm (2 ^ (206 + 1)) = 102034934702015856737 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (206 + 1)) % 2 ^ 256 = 2 ^ (206 + 1) by decide]
  rw [ray_eval_seam_206_hi]
  decide

private theorem ray_seam_206 :
    sle (model_ln_wad_evm (2 ^ (206 + 1) - 1)) (model_ln_wad_evm (2 ^ (206 + 1))) = true := by
  rw [ray_eval_seam_206_lo, ray_eval_seam_206_hi]
  unfold sle
  decide

private theorem wad_seam_206 :
    sle (model_ln_wad_to_wad_evm (2 ^ (206 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (206 + 1))) = true := by
  rw [wad_eval_seam_206_lo, wad_eval_seam_206_hi]
  unfold sle
  decide

private theorem ray_eval_seam_207_lo :
    model_ln_wad_evm (2 ^ (207 + 1) - 1) = 102728081882575802046460435078 := by
  have hlog : Nat.log2 (2 ^ (207 + 1) - 1) = 207 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (207 + 1) - 1) % 2 ^ 256 = 2 ^ (207 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_207_hi :
    model_ln_wad_evm (2 ^ (207 + 1)) = 102728081882575802046460435078 := by
  have hlog : Nat.log2 (2 ^ (207 + 1)) = 208 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (207 + 1)) % 2 ^ 256 = 2 ^ (207 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_207_lo :
    model_ln_wad_to_wad_evm (2 ^ (207 + 1) - 1) = 102728081882575802046 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (207 + 1) - 1) % 2 ^ 256 = 2 ^ (207 + 1) - 1 by decide]
  rw [ray_eval_seam_207_lo]
  decide

private theorem wad_eval_seam_207_hi :
    model_ln_wad_to_wad_evm (2 ^ (207 + 1)) = 102728081882575802046 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (207 + 1)) % 2 ^ 256 = 2 ^ (207 + 1) by decide]
  rw [ray_eval_seam_207_hi]
  decide

private theorem ray_seam_207 :
    sle (model_ln_wad_evm (2 ^ (207 + 1) - 1)) (model_ln_wad_evm (2 ^ (207 + 1))) = true := by
  rw [ray_eval_seam_207_lo, ray_eval_seam_207_hi]
  unfold sle
  decide

private theorem wad_seam_207 :
    sle (model_ln_wad_to_wad_evm (2 ^ (207 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (207 + 1))) = true := by
  rw [wad_eval_seam_207_lo, wad_eval_seam_207_hi]
  unfold sle
  decide

private theorem ray_eval_seam_208_lo :
    model_ln_wad_evm (2 ^ (208 + 1) - 1) = 103421229063135747355877667199 := by
  have hlog : Nat.log2 (2 ^ (208 + 1) - 1) = 208 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (208 + 1) - 1) % 2 ^ 256 = 2 ^ (208 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_208_hi :
    model_ln_wad_evm (2 ^ (208 + 1)) = 103421229063135747355877667200 := by
  have hlog : Nat.log2 (2 ^ (208 + 1)) = 209 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (208 + 1)) % 2 ^ 256 = 2 ^ (208 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_208_lo :
    model_ln_wad_to_wad_evm (2 ^ (208 + 1) - 1) = 103421229063135747355 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (208 + 1) - 1) % 2 ^ 256 = 2 ^ (208 + 1) - 1 by decide]
  rw [ray_eval_seam_208_lo]
  decide

private theorem wad_eval_seam_208_hi :
    model_ln_wad_to_wad_evm (2 ^ (208 + 1)) = 103421229063135747355 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (208 + 1)) % 2 ^ 256 = 2 ^ (208 + 1) by decide]
  rw [ray_eval_seam_208_hi]
  decide

private theorem ray_seam_208 :
    sle (model_ln_wad_evm (2 ^ (208 + 1) - 1)) (model_ln_wad_evm (2 ^ (208 + 1))) = true := by
  rw [ray_eval_seam_208_lo, ray_eval_seam_208_hi]
  unfold sle
  decide

private theorem wad_seam_208 :
    sle (model_ln_wad_to_wad_evm (2 ^ (208 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (208 + 1))) = true := by
  rw [wad_eval_seam_208_lo, wad_eval_seam_208_hi]
  unfold sle
  decide

private theorem ray_eval_seam_209_lo :
    model_ln_wad_evm (2 ^ (209 + 1) - 1) = 104114376243695692665294899321 := by
  have hlog : Nat.log2 (2 ^ (209 + 1) - 1) = 209 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (209 + 1) - 1) % 2 ^ 256 = 2 ^ (209 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_209_hi :
    model_ln_wad_evm (2 ^ (209 + 1)) = 104114376243695692665294899321 := by
  have hlog : Nat.log2 (2 ^ (209 + 1)) = 210 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (209 + 1)) % 2 ^ 256 = 2 ^ (209 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_209_lo :
    model_ln_wad_to_wad_evm (2 ^ (209 + 1) - 1) = 104114376243695692665 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (209 + 1) - 1) % 2 ^ 256 = 2 ^ (209 + 1) - 1 by decide]
  rw [ray_eval_seam_209_lo]
  decide

private theorem wad_eval_seam_209_hi :
    model_ln_wad_to_wad_evm (2 ^ (209 + 1)) = 104114376243695692665 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (209 + 1)) % 2 ^ 256 = 2 ^ (209 + 1) by decide]
  rw [ray_eval_seam_209_hi]
  decide

private theorem ray_seam_209 :
    sle (model_ln_wad_evm (2 ^ (209 + 1) - 1)) (model_ln_wad_evm (2 ^ (209 + 1))) = true := by
  rw [ray_eval_seam_209_lo, ray_eval_seam_209_hi]
  unfold sle
  decide

private theorem wad_seam_209 :
    sle (model_ln_wad_to_wad_evm (2 ^ (209 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (209 + 1))) = true := by
  rw [wad_eval_seam_209_lo, wad_eval_seam_209_hi]
  unfold sle
  decide

private theorem ray_eval_seam_210_lo :
    model_ln_wad_evm (2 ^ (210 + 1) - 1) = 104807523424255637974712131442 := by
  have hlog : Nat.log2 (2 ^ (210 + 1) - 1) = 210 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (210 + 1) - 1) % 2 ^ 256 = 2 ^ (210 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_210_hi :
    model_ln_wad_evm (2 ^ (210 + 1)) = 104807523424255637974712131443 := by
  have hlog : Nat.log2 (2 ^ (210 + 1)) = 211 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (210 + 1)) % 2 ^ 256 = 2 ^ (210 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_210_lo :
    model_ln_wad_to_wad_evm (2 ^ (210 + 1) - 1) = 104807523424255637974 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (210 + 1) - 1) % 2 ^ 256 = 2 ^ (210 + 1) - 1 by decide]
  rw [ray_eval_seam_210_lo]
  decide

private theorem wad_eval_seam_210_hi :
    model_ln_wad_to_wad_evm (2 ^ (210 + 1)) = 104807523424255637974 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (210 + 1)) % 2 ^ 256 = 2 ^ (210 + 1) by decide]
  rw [ray_eval_seam_210_hi]
  decide

private theorem ray_seam_210 :
    sle (model_ln_wad_evm (2 ^ (210 + 1) - 1)) (model_ln_wad_evm (2 ^ (210 + 1))) = true := by
  rw [ray_eval_seam_210_lo, ray_eval_seam_210_hi]
  unfold sle
  decide

private theorem wad_seam_210 :
    sle (model_ln_wad_to_wad_evm (2 ^ (210 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (210 + 1))) = true := by
  rw [wad_eval_seam_210_lo, wad_eval_seam_210_hi]
  unfold sle
  decide

private theorem ray_eval_seam_211_lo :
    model_ln_wad_evm (2 ^ (211 + 1) - 1) = 105500670604815583284129363564 := by
  have hlog : Nat.log2 (2 ^ (211 + 1) - 1) = 211 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (211 + 1) - 1) % 2 ^ 256 = 2 ^ (211 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_211_hi :
    model_ln_wad_evm (2 ^ (211 + 1)) = 105500670604815583284129363564 := by
  have hlog : Nat.log2 (2 ^ (211 + 1)) = 212 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (211 + 1)) % 2 ^ 256 = 2 ^ (211 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_211_lo :
    model_ln_wad_to_wad_evm (2 ^ (211 + 1) - 1) = 105500670604815583284 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (211 + 1) - 1) % 2 ^ 256 = 2 ^ (211 + 1) - 1 by decide]
  rw [ray_eval_seam_211_lo]
  decide

private theorem wad_eval_seam_211_hi :
    model_ln_wad_to_wad_evm (2 ^ (211 + 1)) = 105500670604815583284 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (211 + 1)) % 2 ^ 256 = 2 ^ (211 + 1) by decide]
  rw [ray_eval_seam_211_hi]
  decide

private theorem ray_seam_211 :
    sle (model_ln_wad_evm (2 ^ (211 + 1) - 1)) (model_ln_wad_evm (2 ^ (211 + 1))) = true := by
  rw [ray_eval_seam_211_lo, ray_eval_seam_211_hi]
  unfold sle
  decide

private theorem wad_seam_211 :
    sle (model_ln_wad_to_wad_evm (2 ^ (211 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (211 + 1))) = true := by
  rw [wad_eval_seam_211_lo, wad_eval_seam_211_hi]
  unfold sle
  decide

private theorem ray_eval_seam_212_lo :
    model_ln_wad_evm (2 ^ (212 + 1) - 1) = 106193817785375528593546595685 := by
  have hlog : Nat.log2 (2 ^ (212 + 1) - 1) = 212 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (212 + 1) - 1) % 2 ^ 256 = 2 ^ (212 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_212_hi :
    model_ln_wad_evm (2 ^ (212 + 1)) = 106193817785375528593546595686 := by
  have hlog : Nat.log2 (2 ^ (212 + 1)) = 213 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (212 + 1)) % 2 ^ 256 = 2 ^ (212 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_212_lo :
    model_ln_wad_to_wad_evm (2 ^ (212 + 1) - 1) = 106193817785375528593 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (212 + 1) - 1) % 2 ^ 256 = 2 ^ (212 + 1) - 1 by decide]
  rw [ray_eval_seam_212_lo]
  decide

private theorem wad_eval_seam_212_hi :
    model_ln_wad_to_wad_evm (2 ^ (212 + 1)) = 106193817785375528593 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (212 + 1)) % 2 ^ 256 = 2 ^ (212 + 1) by decide]
  rw [ray_eval_seam_212_hi]
  decide

private theorem ray_seam_212 :
    sle (model_ln_wad_evm (2 ^ (212 + 1) - 1)) (model_ln_wad_evm (2 ^ (212 + 1))) = true := by
  rw [ray_eval_seam_212_lo, ray_eval_seam_212_hi]
  unfold sle
  decide

private theorem wad_seam_212 :
    sle (model_ln_wad_to_wad_evm (2 ^ (212 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (212 + 1))) = true := by
  rw [wad_eval_seam_212_lo, wad_eval_seam_212_hi]
  unfold sle
  decide

private theorem ray_eval_seam_213_lo :
    model_ln_wad_evm (2 ^ (213 + 1) - 1) = 106886964965935473902963827807 := by
  have hlog : Nat.log2 (2 ^ (213 + 1) - 1) = 213 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (213 + 1) - 1) % 2 ^ 256 = 2 ^ (213 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_213_hi :
    model_ln_wad_evm (2 ^ (213 + 1)) = 106886964965935473902963827807 := by
  have hlog : Nat.log2 (2 ^ (213 + 1)) = 214 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (213 + 1)) % 2 ^ 256 = 2 ^ (213 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_213_lo :
    model_ln_wad_to_wad_evm (2 ^ (213 + 1) - 1) = 106886964965935473902 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (213 + 1) - 1) % 2 ^ 256 = 2 ^ (213 + 1) - 1 by decide]
  rw [ray_eval_seam_213_lo]
  decide

private theorem wad_eval_seam_213_hi :
    model_ln_wad_to_wad_evm (2 ^ (213 + 1)) = 106886964965935473902 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (213 + 1)) % 2 ^ 256 = 2 ^ (213 + 1) by decide]
  rw [ray_eval_seam_213_hi]
  decide

private theorem ray_seam_213 :
    sle (model_ln_wad_evm (2 ^ (213 + 1) - 1)) (model_ln_wad_evm (2 ^ (213 + 1))) = true := by
  rw [ray_eval_seam_213_lo, ray_eval_seam_213_hi]
  unfold sle
  decide

private theorem wad_seam_213 :
    sle (model_ln_wad_to_wad_evm (2 ^ (213 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (213 + 1))) = true := by
  rw [wad_eval_seam_213_lo, wad_eval_seam_213_hi]
  unfold sle
  decide

private theorem ray_eval_seam_214_lo :
    model_ln_wad_evm (2 ^ (214 + 1) - 1) = 107580112146495419212381059928 := by
  have hlog : Nat.log2 (2 ^ (214 + 1) - 1) = 214 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (214 + 1) - 1) % 2 ^ 256 = 2 ^ (214 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_214_hi :
    model_ln_wad_evm (2 ^ (214 + 1)) = 107580112146495419212381059929 := by
  have hlog : Nat.log2 (2 ^ (214 + 1)) = 215 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (214 + 1)) % 2 ^ 256 = 2 ^ (214 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_214_lo :
    model_ln_wad_to_wad_evm (2 ^ (214 + 1) - 1) = 107580112146495419212 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (214 + 1) - 1) % 2 ^ 256 = 2 ^ (214 + 1) - 1 by decide]
  rw [ray_eval_seam_214_lo]
  decide

private theorem wad_eval_seam_214_hi :
    model_ln_wad_to_wad_evm (2 ^ (214 + 1)) = 107580112146495419212 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (214 + 1)) % 2 ^ 256 = 2 ^ (214 + 1) by decide]
  rw [ray_eval_seam_214_hi]
  decide

private theorem ray_seam_214 :
    sle (model_ln_wad_evm (2 ^ (214 + 1) - 1)) (model_ln_wad_evm (2 ^ (214 + 1))) = true := by
  rw [ray_eval_seam_214_lo, ray_eval_seam_214_hi]
  unfold sle
  decide

private theorem wad_seam_214 :
    sle (model_ln_wad_to_wad_evm (2 ^ (214 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (214 + 1))) = true := by
  rw [wad_eval_seam_214_lo, wad_eval_seam_214_hi]
  unfold sle
  decide

private theorem ray_eval_seam_215_lo :
    model_ln_wad_evm (2 ^ (215 + 1) - 1) = 108273259327055364521798292049 := by
  have hlog : Nat.log2 (2 ^ (215 + 1) - 1) = 215 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (215 + 1) - 1) % 2 ^ 256 = 2 ^ (215 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_215_hi :
    model_ln_wad_evm (2 ^ (215 + 1)) = 108273259327055364521798292050 := by
  have hlog : Nat.log2 (2 ^ (215 + 1)) = 216 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (215 + 1)) % 2 ^ 256 = 2 ^ (215 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_215_lo :
    model_ln_wad_to_wad_evm (2 ^ (215 + 1) - 1) = 108273259327055364521 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (215 + 1) - 1) % 2 ^ 256 = 2 ^ (215 + 1) - 1 by decide]
  rw [ray_eval_seam_215_lo]
  decide

private theorem wad_eval_seam_215_hi :
    model_ln_wad_to_wad_evm (2 ^ (215 + 1)) = 108273259327055364521 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (215 + 1)) % 2 ^ 256 = 2 ^ (215 + 1) by decide]
  rw [ray_eval_seam_215_hi]
  decide

private theorem ray_seam_215 :
    sle (model_ln_wad_evm (2 ^ (215 + 1) - 1)) (model_ln_wad_evm (2 ^ (215 + 1))) = true := by
  rw [ray_eval_seam_215_lo, ray_eval_seam_215_hi]
  unfold sle
  decide

private theorem wad_seam_215 :
    sle (model_ln_wad_to_wad_evm (2 ^ (215 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (215 + 1))) = true := by
  rw [wad_eval_seam_215_lo, wad_eval_seam_215_hi]
  unfold sle
  decide

private theorem ray_eval_seam_216_lo :
    model_ln_wad_evm (2 ^ (216 + 1) - 1) = 108966406507615309831215524171 := by
  have hlog : Nat.log2 (2 ^ (216 + 1) - 1) = 216 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (216 + 1) - 1) % 2 ^ 256 = 2 ^ (216 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_216_hi :
    model_ln_wad_evm (2 ^ (216 + 1)) = 108966406507615309831215524172 := by
  have hlog : Nat.log2 (2 ^ (216 + 1)) = 217 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (216 + 1)) % 2 ^ 256 = 2 ^ (216 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_216_lo :
    model_ln_wad_to_wad_evm (2 ^ (216 + 1) - 1) = 108966406507615309831 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (216 + 1) - 1) % 2 ^ 256 = 2 ^ (216 + 1) - 1 by decide]
  rw [ray_eval_seam_216_lo]
  decide

private theorem wad_eval_seam_216_hi :
    model_ln_wad_to_wad_evm (2 ^ (216 + 1)) = 108966406507615309831 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (216 + 1)) % 2 ^ 256 = 2 ^ (216 + 1) by decide]
  rw [ray_eval_seam_216_hi]
  decide

private theorem ray_seam_216 :
    sle (model_ln_wad_evm (2 ^ (216 + 1) - 1)) (model_ln_wad_evm (2 ^ (216 + 1))) = true := by
  rw [ray_eval_seam_216_lo, ray_eval_seam_216_hi]
  unfold sle
  decide

private theorem wad_seam_216 :
    sle (model_ln_wad_to_wad_evm (2 ^ (216 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (216 + 1))) = true := by
  rw [wad_eval_seam_216_lo, wad_eval_seam_216_hi]
  unfold sle
  decide

private theorem ray_eval_seam_217_lo :
    model_ln_wad_evm (2 ^ (217 + 1) - 1) = 109659553688175255140632756292 := by
  have hlog : Nat.log2 (2 ^ (217 + 1) - 1) = 217 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (217 + 1) - 1) % 2 ^ 256 = 2 ^ (217 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_217_hi :
    model_ln_wad_evm (2 ^ (217 + 1)) = 109659553688175255140632756293 := by
  have hlog : Nat.log2 (2 ^ (217 + 1)) = 218 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (217 + 1)) % 2 ^ 256 = 2 ^ (217 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_217_lo :
    model_ln_wad_to_wad_evm (2 ^ (217 + 1) - 1) = 109659553688175255140 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (217 + 1) - 1) % 2 ^ 256 = 2 ^ (217 + 1) - 1 by decide]
  rw [ray_eval_seam_217_lo]
  decide

private theorem wad_eval_seam_217_hi :
    model_ln_wad_to_wad_evm (2 ^ (217 + 1)) = 109659553688175255140 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (217 + 1)) % 2 ^ 256 = 2 ^ (217 + 1) by decide]
  rw [ray_eval_seam_217_hi]
  decide

private theorem ray_seam_217 :
    sle (model_ln_wad_evm (2 ^ (217 + 1) - 1)) (model_ln_wad_evm (2 ^ (217 + 1))) = true := by
  rw [ray_eval_seam_217_lo, ray_eval_seam_217_hi]
  unfold sle
  decide

private theorem wad_seam_217 :
    sle (model_ln_wad_to_wad_evm (2 ^ (217 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (217 + 1))) = true := by
  rw [wad_eval_seam_217_lo, wad_eval_seam_217_hi]
  unfold sle
  decide

private theorem ray_eval_seam_218_lo :
    model_ln_wad_evm (2 ^ (218 + 1) - 1) = 110352700868735200450049988414 := by
  have hlog : Nat.log2 (2 ^ (218 + 1) - 1) = 218 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (218 + 1) - 1) % 2 ^ 256 = 2 ^ (218 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_218_hi :
    model_ln_wad_evm (2 ^ (218 + 1)) = 110352700868735200450049988415 := by
  have hlog : Nat.log2 (2 ^ (218 + 1)) = 219 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (218 + 1)) % 2 ^ 256 = 2 ^ (218 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_218_lo :
    model_ln_wad_to_wad_evm (2 ^ (218 + 1) - 1) = 110352700868735200450 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (218 + 1) - 1) % 2 ^ 256 = 2 ^ (218 + 1) - 1 by decide]
  rw [ray_eval_seam_218_lo]
  decide

private theorem wad_eval_seam_218_hi :
    model_ln_wad_to_wad_evm (2 ^ (218 + 1)) = 110352700868735200450 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (218 + 1)) % 2 ^ 256 = 2 ^ (218 + 1) by decide]
  rw [ray_eval_seam_218_hi]
  decide

private theorem ray_seam_218 :
    sle (model_ln_wad_evm (2 ^ (218 + 1) - 1)) (model_ln_wad_evm (2 ^ (218 + 1))) = true := by
  rw [ray_eval_seam_218_lo, ray_eval_seam_218_hi]
  unfold sle
  decide

private theorem wad_seam_218 :
    sle (model_ln_wad_to_wad_evm (2 ^ (218 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (218 + 1))) = true := by
  rw [wad_eval_seam_218_lo, wad_eval_seam_218_hi]
  unfold sle
  decide

private theorem ray_eval_seam_219_lo :
    model_ln_wad_evm (2 ^ (219 + 1) - 1) = 111045848049295145759467220535 := by
  have hlog : Nat.log2 (2 ^ (219 + 1) - 1) = 219 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (219 + 1) - 1) % 2 ^ 256 = 2 ^ (219 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_219_hi :
    model_ln_wad_evm (2 ^ (219 + 1)) = 111045848049295145759467220536 := by
  have hlog : Nat.log2 (2 ^ (219 + 1)) = 220 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (219 + 1)) % 2 ^ 256 = 2 ^ (219 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_219_lo :
    model_ln_wad_to_wad_evm (2 ^ (219 + 1) - 1) = 111045848049295145759 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (219 + 1) - 1) % 2 ^ 256 = 2 ^ (219 + 1) - 1 by decide]
  rw [ray_eval_seam_219_lo]
  decide

private theorem wad_eval_seam_219_hi :
    model_ln_wad_to_wad_evm (2 ^ (219 + 1)) = 111045848049295145759 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (219 + 1)) % 2 ^ 256 = 2 ^ (219 + 1) by decide]
  rw [ray_eval_seam_219_hi]
  decide

private theorem ray_seam_219 :
    sle (model_ln_wad_evm (2 ^ (219 + 1) - 1)) (model_ln_wad_evm (2 ^ (219 + 1))) = true := by
  rw [ray_eval_seam_219_lo, ray_eval_seam_219_hi]
  unfold sle
  decide

private theorem wad_seam_219 :
    sle (model_ln_wad_to_wad_evm (2 ^ (219 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (219 + 1))) = true := by
  rw [wad_eval_seam_219_lo, wad_eval_seam_219_hi]
  unfold sle
  decide

private theorem ray_eval_seam_220_lo :
    model_ln_wad_evm (2 ^ (220 + 1) - 1) = 111738995229855091068884452657 := by
  have hlog : Nat.log2 (2 ^ (220 + 1) - 1) = 220 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (220 + 1) - 1) % 2 ^ 256 = 2 ^ (220 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_220_hi :
    model_ln_wad_evm (2 ^ (220 + 1)) = 111738995229855091068884452657 := by
  have hlog : Nat.log2 (2 ^ (220 + 1)) = 221 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (220 + 1)) % 2 ^ 256 = 2 ^ (220 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_220_lo :
    model_ln_wad_to_wad_evm (2 ^ (220 + 1) - 1) = 111738995229855091068 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (220 + 1) - 1) % 2 ^ 256 = 2 ^ (220 + 1) - 1 by decide]
  rw [ray_eval_seam_220_lo]
  decide

private theorem wad_eval_seam_220_hi :
    model_ln_wad_to_wad_evm (2 ^ (220 + 1)) = 111738995229855091068 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (220 + 1)) % 2 ^ 256 = 2 ^ (220 + 1) by decide]
  rw [ray_eval_seam_220_hi]
  decide

private theorem ray_seam_220 :
    sle (model_ln_wad_evm (2 ^ (220 + 1) - 1)) (model_ln_wad_evm (2 ^ (220 + 1))) = true := by
  rw [ray_eval_seam_220_lo, ray_eval_seam_220_hi]
  unfold sle
  decide

private theorem wad_seam_220 :
    sle (model_ln_wad_to_wad_evm (2 ^ (220 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (220 + 1))) = true := by
  rw [wad_eval_seam_220_lo, wad_eval_seam_220_hi]
  unfold sle
  decide

private theorem ray_eval_seam_221_lo :
    model_ln_wad_evm (2 ^ (221 + 1) - 1) = 112432142410415036378301684778 := by
  have hlog : Nat.log2 (2 ^ (221 + 1) - 1) = 221 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (221 + 1) - 1) % 2 ^ 256 = 2 ^ (221 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_221_hi :
    model_ln_wad_evm (2 ^ (221 + 1)) = 112432142410415036378301684779 := by
  have hlog : Nat.log2 (2 ^ (221 + 1)) = 222 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (221 + 1)) % 2 ^ 256 = 2 ^ (221 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_221_lo :
    model_ln_wad_to_wad_evm (2 ^ (221 + 1) - 1) = 112432142410415036378 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (221 + 1) - 1) % 2 ^ 256 = 2 ^ (221 + 1) - 1 by decide]
  rw [ray_eval_seam_221_lo]
  decide

private theorem wad_eval_seam_221_hi :
    model_ln_wad_to_wad_evm (2 ^ (221 + 1)) = 112432142410415036378 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (221 + 1)) % 2 ^ 256 = 2 ^ (221 + 1) by decide]
  rw [ray_eval_seam_221_hi]
  decide

private theorem ray_seam_221 :
    sle (model_ln_wad_evm (2 ^ (221 + 1) - 1)) (model_ln_wad_evm (2 ^ (221 + 1))) = true := by
  rw [ray_eval_seam_221_lo, ray_eval_seam_221_hi]
  unfold sle
  decide

private theorem wad_seam_221 :
    sle (model_ln_wad_to_wad_evm (2 ^ (221 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (221 + 1))) = true := by
  rw [wad_eval_seam_221_lo, wad_eval_seam_221_hi]
  unfold sle
  decide

private theorem ray_eval_seam_222_lo :
    model_ln_wad_evm (2 ^ (222 + 1) - 1) = 113125289590974981687718916900 := by
  have hlog : Nat.log2 (2 ^ (222 + 1) - 1) = 222 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (222 + 1) - 1) % 2 ^ 256 = 2 ^ (222 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_222_hi :
    model_ln_wad_evm (2 ^ (222 + 1)) = 113125289590974981687718916900 := by
  have hlog : Nat.log2 (2 ^ (222 + 1)) = 223 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (222 + 1)) % 2 ^ 256 = 2 ^ (222 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_222_lo :
    model_ln_wad_to_wad_evm (2 ^ (222 + 1) - 1) = 113125289590974981687 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (222 + 1) - 1) % 2 ^ 256 = 2 ^ (222 + 1) - 1 by decide]
  rw [ray_eval_seam_222_lo]
  decide

private theorem wad_eval_seam_222_hi :
    model_ln_wad_to_wad_evm (2 ^ (222 + 1)) = 113125289590974981687 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (222 + 1)) % 2 ^ 256 = 2 ^ (222 + 1) by decide]
  rw [ray_eval_seam_222_hi]
  decide

private theorem ray_seam_222 :
    sle (model_ln_wad_evm (2 ^ (222 + 1) - 1)) (model_ln_wad_evm (2 ^ (222 + 1))) = true := by
  rw [ray_eval_seam_222_lo, ray_eval_seam_222_hi]
  unfold sle
  decide

private theorem wad_seam_222 :
    sle (model_ln_wad_to_wad_evm (2 ^ (222 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (222 + 1))) = true := by
  rw [wad_eval_seam_222_lo, wad_eval_seam_222_hi]
  unfold sle
  decide

private theorem ray_eval_seam_223_lo :
    model_ln_wad_evm (2 ^ (223 + 1) - 1) = 113818436771534926997136149021 := by
  have hlog : Nat.log2 (2 ^ (223 + 1) - 1) = 223 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (223 + 1) - 1) % 2 ^ 256 = 2 ^ (223 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_223_hi :
    model_ln_wad_evm (2 ^ (223 + 1)) = 113818436771534926997136149022 := by
  have hlog : Nat.log2 (2 ^ (223 + 1)) = 224 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (223 + 1)) % 2 ^ 256 = 2 ^ (223 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_223_lo :
    model_ln_wad_to_wad_evm (2 ^ (223 + 1) - 1) = 113818436771534926997 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (223 + 1) - 1) % 2 ^ 256 = 2 ^ (223 + 1) - 1 by decide]
  rw [ray_eval_seam_223_lo]
  decide

private theorem wad_eval_seam_223_hi :
    model_ln_wad_to_wad_evm (2 ^ (223 + 1)) = 113818436771534926997 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (223 + 1)) % 2 ^ 256 = 2 ^ (223 + 1) by decide]
  rw [ray_eval_seam_223_hi]
  decide

private theorem ray_seam_223 :
    sle (model_ln_wad_evm (2 ^ (223 + 1) - 1)) (model_ln_wad_evm (2 ^ (223 + 1))) = true := by
  rw [ray_eval_seam_223_lo, ray_eval_seam_223_hi]
  unfold sle
  decide

private theorem wad_seam_223 :
    sle (model_ln_wad_to_wad_evm (2 ^ (223 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (223 + 1))) = true := by
  rw [wad_eval_seam_223_lo, wad_eval_seam_223_hi]
  unfold sle
  decide

private theorem ray_eval_seam_224_lo :
    model_ln_wad_evm (2 ^ (224 + 1) - 1) = 114511583952094872306553381143 := by
  have hlog : Nat.log2 (2 ^ (224 + 1) - 1) = 224 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (224 + 1) - 1) % 2 ^ 256 = 2 ^ (224 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_224_hi :
    model_ln_wad_evm (2 ^ (224 + 1)) = 114511583952094872306553381143 := by
  have hlog : Nat.log2 (2 ^ (224 + 1)) = 225 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (224 + 1)) % 2 ^ 256 = 2 ^ (224 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_224_lo :
    model_ln_wad_to_wad_evm (2 ^ (224 + 1) - 1) = 114511583952094872306 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (224 + 1) - 1) % 2 ^ 256 = 2 ^ (224 + 1) - 1 by decide]
  rw [ray_eval_seam_224_lo]
  decide

private theorem wad_eval_seam_224_hi :
    model_ln_wad_to_wad_evm (2 ^ (224 + 1)) = 114511583952094872306 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (224 + 1)) % 2 ^ 256 = 2 ^ (224 + 1) by decide]
  rw [ray_eval_seam_224_hi]
  decide

private theorem ray_seam_224 :
    sle (model_ln_wad_evm (2 ^ (224 + 1) - 1)) (model_ln_wad_evm (2 ^ (224 + 1))) = true := by
  rw [ray_eval_seam_224_lo, ray_eval_seam_224_hi]
  unfold sle
  decide

private theorem wad_seam_224 :
    sle (model_ln_wad_to_wad_evm (2 ^ (224 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (224 + 1))) = true := by
  rw [wad_eval_seam_224_lo, wad_eval_seam_224_hi]
  unfold sle
  decide

private theorem ray_eval_seam_225_lo :
    model_ln_wad_evm (2 ^ (225 + 1) - 1) = 115204731132654817615970613264 := by
  have hlog : Nat.log2 (2 ^ (225 + 1) - 1) = 225 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (225 + 1) - 1) % 2 ^ 256 = 2 ^ (225 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_225_hi :
    model_ln_wad_evm (2 ^ (225 + 1)) = 115204731132654817615970613265 := by
  have hlog : Nat.log2 (2 ^ (225 + 1)) = 226 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (225 + 1)) % 2 ^ 256 = 2 ^ (225 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_225_lo :
    model_ln_wad_to_wad_evm (2 ^ (225 + 1) - 1) = 115204731132654817615 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (225 + 1) - 1) % 2 ^ 256 = 2 ^ (225 + 1) - 1 by decide]
  rw [ray_eval_seam_225_lo]
  decide

private theorem wad_eval_seam_225_hi :
    model_ln_wad_to_wad_evm (2 ^ (225 + 1)) = 115204731132654817615 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (225 + 1)) % 2 ^ 256 = 2 ^ (225 + 1) by decide]
  rw [ray_eval_seam_225_hi]
  decide

private theorem ray_seam_225 :
    sle (model_ln_wad_evm (2 ^ (225 + 1) - 1)) (model_ln_wad_evm (2 ^ (225 + 1))) = true := by
  rw [ray_eval_seam_225_lo, ray_eval_seam_225_hi]
  unfold sle
  decide

private theorem wad_seam_225 :
    sle (model_ln_wad_to_wad_evm (2 ^ (225 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (225 + 1))) = true := by
  rw [wad_eval_seam_225_lo, wad_eval_seam_225_hi]
  unfold sle
  decide

private theorem ray_eval_seam_226_lo :
    model_ln_wad_evm (2 ^ (226 + 1) - 1) = 115897878313214762925387845386 := by
  have hlog : Nat.log2 (2 ^ (226 + 1) - 1) = 226 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (226 + 1) - 1) % 2 ^ 256 = 2 ^ (226 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_226_hi :
    model_ln_wad_evm (2 ^ (226 + 1)) = 115897878313214762925387845386 := by
  have hlog : Nat.log2 (2 ^ (226 + 1)) = 227 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (226 + 1)) % 2 ^ 256 = 2 ^ (226 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_226_lo :
    model_ln_wad_to_wad_evm (2 ^ (226 + 1) - 1) = 115897878313214762925 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (226 + 1) - 1) % 2 ^ 256 = 2 ^ (226 + 1) - 1 by decide]
  rw [ray_eval_seam_226_lo]
  decide

private theorem wad_eval_seam_226_hi :
    model_ln_wad_to_wad_evm (2 ^ (226 + 1)) = 115897878313214762925 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (226 + 1)) % 2 ^ 256 = 2 ^ (226 + 1) by decide]
  rw [ray_eval_seam_226_hi]
  decide

private theorem ray_seam_226 :
    sle (model_ln_wad_evm (2 ^ (226 + 1) - 1)) (model_ln_wad_evm (2 ^ (226 + 1))) = true := by
  rw [ray_eval_seam_226_lo, ray_eval_seam_226_hi]
  unfold sle
  decide

private theorem wad_seam_226 :
    sle (model_ln_wad_to_wad_evm (2 ^ (226 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (226 + 1))) = true := by
  rw [wad_eval_seam_226_lo, wad_eval_seam_226_hi]
  unfold sle
  decide

private theorem ray_eval_seam_227_lo :
    model_ln_wad_evm (2 ^ (227 + 1) - 1) = 116591025493774708234805077507 := by
  have hlog : Nat.log2 (2 ^ (227 + 1) - 1) = 227 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (227 + 1) - 1) % 2 ^ 256 = 2 ^ (227 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_227_hi :
    model_ln_wad_evm (2 ^ (227 + 1)) = 116591025493774708234805077508 := by
  have hlog : Nat.log2 (2 ^ (227 + 1)) = 228 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (227 + 1)) % 2 ^ 256 = 2 ^ (227 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_227_lo :
    model_ln_wad_to_wad_evm (2 ^ (227 + 1) - 1) = 116591025493774708234 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (227 + 1) - 1) % 2 ^ 256 = 2 ^ (227 + 1) - 1 by decide]
  rw [ray_eval_seam_227_lo]
  decide

private theorem wad_eval_seam_227_hi :
    model_ln_wad_to_wad_evm (2 ^ (227 + 1)) = 116591025493774708234 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (227 + 1)) % 2 ^ 256 = 2 ^ (227 + 1) by decide]
  rw [ray_eval_seam_227_hi]
  decide

private theorem ray_seam_227 :
    sle (model_ln_wad_evm (2 ^ (227 + 1) - 1)) (model_ln_wad_evm (2 ^ (227 + 1))) = true := by
  rw [ray_eval_seam_227_lo, ray_eval_seam_227_hi]
  unfold sle
  decide

private theorem wad_seam_227 :
    sle (model_ln_wad_to_wad_evm (2 ^ (227 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (227 + 1))) = true := by
  rw [wad_eval_seam_227_lo, wad_eval_seam_227_hi]
  unfold sle
  decide

private theorem ray_eval_seam_228_lo :
    model_ln_wad_evm (2 ^ (228 + 1) - 1) = 117284172674334653544222309628 := by
  have hlog : Nat.log2 (2 ^ (228 + 1) - 1) = 228 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (228 + 1) - 1) % 2 ^ 256 = 2 ^ (228 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_228_hi :
    model_ln_wad_evm (2 ^ (228 + 1)) = 117284172674334653544222309629 := by
  have hlog : Nat.log2 (2 ^ (228 + 1)) = 229 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (228 + 1)) % 2 ^ 256 = 2 ^ (228 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_228_lo :
    model_ln_wad_to_wad_evm (2 ^ (228 + 1) - 1) = 117284172674334653544 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (228 + 1) - 1) % 2 ^ 256 = 2 ^ (228 + 1) - 1 by decide]
  rw [ray_eval_seam_228_lo]
  decide

private theorem wad_eval_seam_228_hi :
    model_ln_wad_to_wad_evm (2 ^ (228 + 1)) = 117284172674334653544 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (228 + 1)) % 2 ^ 256 = 2 ^ (228 + 1) by decide]
  rw [ray_eval_seam_228_hi]
  decide

private theorem ray_seam_228 :
    sle (model_ln_wad_evm (2 ^ (228 + 1) - 1)) (model_ln_wad_evm (2 ^ (228 + 1))) = true := by
  rw [ray_eval_seam_228_lo, ray_eval_seam_228_hi]
  unfold sle
  decide

private theorem wad_seam_228 :
    sle (model_ln_wad_to_wad_evm (2 ^ (228 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (228 + 1))) = true := by
  rw [wad_eval_seam_228_lo, wad_eval_seam_228_hi]
  unfold sle
  decide

private theorem ray_eval_seam_229_lo :
    model_ln_wad_evm (2 ^ (229 + 1) - 1) = 117977319854894598853639541750 := by
  have hlog : Nat.log2 (2 ^ (229 + 1) - 1) = 229 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (229 + 1) - 1) % 2 ^ 256 = 2 ^ (229 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_229_hi :
    model_ln_wad_evm (2 ^ (229 + 1)) = 117977319854894598853639541751 := by
  have hlog : Nat.log2 (2 ^ (229 + 1)) = 230 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (229 + 1)) % 2 ^ 256 = 2 ^ (229 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_229_lo :
    model_ln_wad_to_wad_evm (2 ^ (229 + 1) - 1) = 117977319854894598853 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (229 + 1) - 1) % 2 ^ 256 = 2 ^ (229 + 1) - 1 by decide]
  rw [ray_eval_seam_229_lo]
  decide

private theorem wad_eval_seam_229_hi :
    model_ln_wad_to_wad_evm (2 ^ (229 + 1)) = 117977319854894598853 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (229 + 1)) % 2 ^ 256 = 2 ^ (229 + 1) by decide]
  rw [ray_eval_seam_229_hi]
  decide

private theorem ray_seam_229 :
    sle (model_ln_wad_evm (2 ^ (229 + 1) - 1)) (model_ln_wad_evm (2 ^ (229 + 1))) = true := by
  rw [ray_eval_seam_229_lo, ray_eval_seam_229_hi]
  unfold sle
  decide

private theorem wad_seam_229 :
    sle (model_ln_wad_to_wad_evm (2 ^ (229 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (229 + 1))) = true := by
  rw [wad_eval_seam_229_lo, wad_eval_seam_229_hi]
  unfold sle
  decide

private theorem ray_eval_seam_230_lo :
    model_ln_wad_evm (2 ^ (230 + 1) - 1) = 118670467035454544163056773871 := by
  have hlog : Nat.log2 (2 ^ (230 + 1) - 1) = 230 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (230 + 1) - 1) % 2 ^ 256 = 2 ^ (230 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_230_hi :
    model_ln_wad_evm (2 ^ (230 + 1)) = 118670467035454544163056773872 := by
  have hlog : Nat.log2 (2 ^ (230 + 1)) = 231 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (230 + 1)) % 2 ^ 256 = 2 ^ (230 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_230_lo :
    model_ln_wad_to_wad_evm (2 ^ (230 + 1) - 1) = 118670467035454544163 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (230 + 1) - 1) % 2 ^ 256 = 2 ^ (230 + 1) - 1 by decide]
  rw [ray_eval_seam_230_lo]
  decide

private theorem wad_eval_seam_230_hi :
    model_ln_wad_to_wad_evm (2 ^ (230 + 1)) = 118670467035454544163 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (230 + 1)) % 2 ^ 256 = 2 ^ (230 + 1) by decide]
  rw [ray_eval_seam_230_hi]
  decide

private theorem ray_seam_230 :
    sle (model_ln_wad_evm (2 ^ (230 + 1) - 1)) (model_ln_wad_evm (2 ^ (230 + 1))) = true := by
  rw [ray_eval_seam_230_lo, ray_eval_seam_230_hi]
  unfold sle
  decide

private theorem wad_seam_230 :
    sle (model_ln_wad_to_wad_evm (2 ^ (230 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (230 + 1))) = true := by
  rw [wad_eval_seam_230_lo, wad_eval_seam_230_hi]
  unfold sle
  decide

private theorem ray_eval_seam_231_lo :
    model_ln_wad_evm (2 ^ (231 + 1) - 1) = 119363614216014489472474005993 := by
  have hlog : Nat.log2 (2 ^ (231 + 1) - 1) = 231 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (231 + 1) - 1) % 2 ^ 256 = 2 ^ (231 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_231_hi :
    model_ln_wad_evm (2 ^ (231 + 1)) = 119363614216014489472474005993 := by
  have hlog : Nat.log2 (2 ^ (231 + 1)) = 232 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (231 + 1)) % 2 ^ 256 = 2 ^ (231 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_231_lo :
    model_ln_wad_to_wad_evm (2 ^ (231 + 1) - 1) = 119363614216014489472 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (231 + 1) - 1) % 2 ^ 256 = 2 ^ (231 + 1) - 1 by decide]
  rw [ray_eval_seam_231_lo]
  decide

private theorem wad_eval_seam_231_hi :
    model_ln_wad_to_wad_evm (2 ^ (231 + 1)) = 119363614216014489472 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (231 + 1)) % 2 ^ 256 = 2 ^ (231 + 1) by decide]
  rw [ray_eval_seam_231_hi]
  decide

private theorem ray_seam_231 :
    sle (model_ln_wad_evm (2 ^ (231 + 1) - 1)) (model_ln_wad_evm (2 ^ (231 + 1))) = true := by
  rw [ray_eval_seam_231_lo, ray_eval_seam_231_hi]
  unfold sle
  decide

private theorem wad_seam_231 :
    sle (model_ln_wad_to_wad_evm (2 ^ (231 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (231 + 1))) = true := by
  rw [wad_eval_seam_231_lo, wad_eval_seam_231_hi]
  unfold sle
  decide

private theorem ray_eval_seam_232_lo :
    model_ln_wad_evm (2 ^ (232 + 1) - 1) = 120056761396574434781891238114 := by
  have hlog : Nat.log2 (2 ^ (232 + 1) - 1) = 232 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (232 + 1) - 1) % 2 ^ 256 = 2 ^ (232 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_232_hi :
    model_ln_wad_evm (2 ^ (232 + 1)) = 120056761396574434781891238115 := by
  have hlog : Nat.log2 (2 ^ (232 + 1)) = 233 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (232 + 1)) % 2 ^ 256 = 2 ^ (232 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_232_lo :
    model_ln_wad_to_wad_evm (2 ^ (232 + 1) - 1) = 120056761396574434781 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (232 + 1) - 1) % 2 ^ 256 = 2 ^ (232 + 1) - 1 by decide]
  rw [ray_eval_seam_232_lo]
  decide

private theorem wad_eval_seam_232_hi :
    model_ln_wad_to_wad_evm (2 ^ (232 + 1)) = 120056761396574434781 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (232 + 1)) % 2 ^ 256 = 2 ^ (232 + 1) by decide]
  rw [ray_eval_seam_232_hi]
  decide

private theorem ray_seam_232 :
    sle (model_ln_wad_evm (2 ^ (232 + 1) - 1)) (model_ln_wad_evm (2 ^ (232 + 1))) = true := by
  rw [ray_eval_seam_232_lo, ray_eval_seam_232_hi]
  unfold sle
  decide

private theorem wad_seam_232 :
    sle (model_ln_wad_to_wad_evm (2 ^ (232 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (232 + 1))) = true := by
  rw [wad_eval_seam_232_lo, wad_eval_seam_232_hi]
  unfold sle
  decide

private theorem ray_eval_seam_233_lo :
    model_ln_wad_evm (2 ^ (233 + 1) - 1) = 120749908577134380091308470236 := by
  have hlog : Nat.log2 (2 ^ (233 + 1) - 1) = 233 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (233 + 1) - 1) % 2 ^ 256 = 2 ^ (233 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_233_hi :
    model_ln_wad_evm (2 ^ (233 + 1)) = 120749908577134380091308470236 := by
  have hlog : Nat.log2 (2 ^ (233 + 1)) = 234 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (233 + 1)) % 2 ^ 256 = 2 ^ (233 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_233_lo :
    model_ln_wad_to_wad_evm (2 ^ (233 + 1) - 1) = 120749908577134380091 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (233 + 1) - 1) % 2 ^ 256 = 2 ^ (233 + 1) - 1 by decide]
  rw [ray_eval_seam_233_lo]
  decide

private theorem wad_eval_seam_233_hi :
    model_ln_wad_to_wad_evm (2 ^ (233 + 1)) = 120749908577134380091 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (233 + 1)) % 2 ^ 256 = 2 ^ (233 + 1) by decide]
  rw [ray_eval_seam_233_hi]
  decide

private theorem ray_seam_233 :
    sle (model_ln_wad_evm (2 ^ (233 + 1) - 1)) (model_ln_wad_evm (2 ^ (233 + 1))) = true := by
  rw [ray_eval_seam_233_lo, ray_eval_seam_233_hi]
  unfold sle
  decide

private theorem wad_seam_233 :
    sle (model_ln_wad_to_wad_evm (2 ^ (233 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (233 + 1))) = true := by
  rw [wad_eval_seam_233_lo, wad_eval_seam_233_hi]
  unfold sle
  decide

private theorem ray_eval_seam_234_lo :
    model_ln_wad_evm (2 ^ (234 + 1) - 1) = 121443055757694325400725702357 := by
  have hlog : Nat.log2 (2 ^ (234 + 1) - 1) = 234 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (234 + 1) - 1) % 2 ^ 256 = 2 ^ (234 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_234_hi :
    model_ln_wad_evm (2 ^ (234 + 1)) = 121443055757694325400725702358 := by
  have hlog : Nat.log2 (2 ^ (234 + 1)) = 235 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (234 + 1)) % 2 ^ 256 = 2 ^ (234 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_234_lo :
    model_ln_wad_to_wad_evm (2 ^ (234 + 1) - 1) = 121443055757694325400 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (234 + 1) - 1) % 2 ^ 256 = 2 ^ (234 + 1) - 1 by decide]
  rw [ray_eval_seam_234_lo]
  decide

private theorem wad_eval_seam_234_hi :
    model_ln_wad_to_wad_evm (2 ^ (234 + 1)) = 121443055757694325400 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (234 + 1)) % 2 ^ 256 = 2 ^ (234 + 1) by decide]
  rw [ray_eval_seam_234_hi]
  decide

private theorem ray_seam_234 :
    sle (model_ln_wad_evm (2 ^ (234 + 1) - 1)) (model_ln_wad_evm (2 ^ (234 + 1))) = true := by
  rw [ray_eval_seam_234_lo, ray_eval_seam_234_hi]
  unfold sle
  decide

private theorem wad_seam_234 :
    sle (model_ln_wad_to_wad_evm (2 ^ (234 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (234 + 1))) = true := by
  rw [wad_eval_seam_234_lo, wad_eval_seam_234_hi]
  unfold sle
  decide

private theorem ray_eval_seam_235_lo :
    model_ln_wad_evm (2 ^ (235 + 1) - 1) = 122136202938254270710142934479 := by
  have hlog : Nat.log2 (2 ^ (235 + 1) - 1) = 235 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (235 + 1) - 1) % 2 ^ 256 = 2 ^ (235 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_235_hi :
    model_ln_wad_evm (2 ^ (235 + 1)) = 122136202938254270710142934479 := by
  have hlog : Nat.log2 (2 ^ (235 + 1)) = 236 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (235 + 1)) % 2 ^ 256 = 2 ^ (235 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_235_lo :
    model_ln_wad_to_wad_evm (2 ^ (235 + 1) - 1) = 122136202938254270710 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (235 + 1) - 1) % 2 ^ 256 = 2 ^ (235 + 1) - 1 by decide]
  rw [ray_eval_seam_235_lo]
  decide

private theorem wad_eval_seam_235_hi :
    model_ln_wad_to_wad_evm (2 ^ (235 + 1)) = 122136202938254270710 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (235 + 1)) % 2 ^ 256 = 2 ^ (235 + 1) by decide]
  rw [ray_eval_seam_235_hi]
  decide

private theorem ray_seam_235 :
    sle (model_ln_wad_evm (2 ^ (235 + 1) - 1)) (model_ln_wad_evm (2 ^ (235 + 1))) = true := by
  rw [ray_eval_seam_235_lo, ray_eval_seam_235_hi]
  unfold sle
  decide

private theorem wad_seam_235 :
    sle (model_ln_wad_to_wad_evm (2 ^ (235 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (235 + 1))) = true := by
  rw [wad_eval_seam_235_lo, wad_eval_seam_235_hi]
  unfold sle
  decide

private theorem ray_eval_seam_236_lo :
    model_ln_wad_evm (2 ^ (236 + 1) - 1) = 122829350118814216019560166600 := by
  have hlog : Nat.log2 (2 ^ (236 + 1) - 1) = 236 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (236 + 1) - 1) % 2 ^ 256 = 2 ^ (236 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_236_hi :
    model_ln_wad_evm (2 ^ (236 + 1)) = 122829350118814216019560166601 := by
  have hlog : Nat.log2 (2 ^ (236 + 1)) = 237 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (236 + 1)) % 2 ^ 256 = 2 ^ (236 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_236_lo :
    model_ln_wad_to_wad_evm (2 ^ (236 + 1) - 1) = 122829350118814216019 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (236 + 1) - 1) % 2 ^ 256 = 2 ^ (236 + 1) - 1 by decide]
  rw [ray_eval_seam_236_lo]
  decide

private theorem wad_eval_seam_236_hi :
    model_ln_wad_to_wad_evm (2 ^ (236 + 1)) = 122829350118814216019 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (236 + 1)) % 2 ^ 256 = 2 ^ (236 + 1) by decide]
  rw [ray_eval_seam_236_hi]
  decide

private theorem ray_seam_236 :
    sle (model_ln_wad_evm (2 ^ (236 + 1) - 1)) (model_ln_wad_evm (2 ^ (236 + 1))) = true := by
  rw [ray_eval_seam_236_lo, ray_eval_seam_236_hi]
  unfold sle
  decide

private theorem wad_seam_236 :
    sle (model_ln_wad_to_wad_evm (2 ^ (236 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (236 + 1))) = true := by
  rw [wad_eval_seam_236_lo, wad_eval_seam_236_hi]
  unfold sle
  decide

private theorem ray_eval_seam_237_lo :
    model_ln_wad_evm (2 ^ (237 + 1) - 1) = 123522497299374161328977398722 := by
  have hlog : Nat.log2 (2 ^ (237 + 1) - 1) = 237 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (237 + 1) - 1) % 2 ^ 256 = 2 ^ (237 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_237_hi :
    model_ln_wad_evm (2 ^ (237 + 1)) = 123522497299374161328977398722 := by
  have hlog : Nat.log2 (2 ^ (237 + 1)) = 238 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (237 + 1)) % 2 ^ 256 = 2 ^ (237 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_237_lo :
    model_ln_wad_to_wad_evm (2 ^ (237 + 1) - 1) = 123522497299374161328 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (237 + 1) - 1) % 2 ^ 256 = 2 ^ (237 + 1) - 1 by decide]
  rw [ray_eval_seam_237_lo]
  decide

private theorem wad_eval_seam_237_hi :
    model_ln_wad_to_wad_evm (2 ^ (237 + 1)) = 123522497299374161328 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (237 + 1)) % 2 ^ 256 = 2 ^ (237 + 1) by decide]
  rw [ray_eval_seam_237_hi]
  decide

private theorem ray_seam_237 :
    sle (model_ln_wad_evm (2 ^ (237 + 1) - 1)) (model_ln_wad_evm (2 ^ (237 + 1))) = true := by
  rw [ray_eval_seam_237_lo, ray_eval_seam_237_hi]
  unfold sle
  decide

private theorem wad_seam_237 :
    sle (model_ln_wad_to_wad_evm (2 ^ (237 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (237 + 1))) = true := by
  rw [wad_eval_seam_237_lo, wad_eval_seam_237_hi]
  unfold sle
  decide

private theorem ray_eval_seam_238_lo :
    model_ln_wad_evm (2 ^ (238 + 1) - 1) = 124215644479934106638394630843 := by
  have hlog : Nat.log2 (2 ^ (238 + 1) - 1) = 238 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (238 + 1) - 1) % 2 ^ 256 = 2 ^ (238 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_238_hi :
    model_ln_wad_evm (2 ^ (238 + 1)) = 124215644479934106638394630844 := by
  have hlog : Nat.log2 (2 ^ (238 + 1)) = 239 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (238 + 1)) % 2 ^ 256 = 2 ^ (238 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_238_lo :
    model_ln_wad_to_wad_evm (2 ^ (238 + 1) - 1) = 124215644479934106638 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (238 + 1) - 1) % 2 ^ 256 = 2 ^ (238 + 1) - 1 by decide]
  rw [ray_eval_seam_238_lo]
  decide

private theorem wad_eval_seam_238_hi :
    model_ln_wad_to_wad_evm (2 ^ (238 + 1)) = 124215644479934106638 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (238 + 1)) % 2 ^ 256 = 2 ^ (238 + 1) by decide]
  rw [ray_eval_seam_238_hi]
  decide

private theorem ray_seam_238 :
    sle (model_ln_wad_evm (2 ^ (238 + 1) - 1)) (model_ln_wad_evm (2 ^ (238 + 1))) = true := by
  rw [ray_eval_seam_238_lo, ray_eval_seam_238_hi]
  unfold sle
  decide

private theorem wad_seam_238 :
    sle (model_ln_wad_to_wad_evm (2 ^ (238 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (238 + 1))) = true := by
  rw [wad_eval_seam_238_lo, wad_eval_seam_238_hi]
  unfold sle
  decide

private theorem ray_eval_seam_239_lo :
    model_ln_wad_evm (2 ^ (239 + 1) - 1) = 124908791660494051947811862964 := by
  have hlog : Nat.log2 (2 ^ (239 + 1) - 1) = 239 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (239 + 1) - 1) % 2 ^ 256 = 2 ^ (239 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_239_hi :
    model_ln_wad_evm (2 ^ (239 + 1)) = 124908791660494051947811862965 := by
  have hlog : Nat.log2 (2 ^ (239 + 1)) = 240 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (239 + 1)) % 2 ^ 256 = 2 ^ (239 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_239_lo :
    model_ln_wad_to_wad_evm (2 ^ (239 + 1) - 1) = 124908791660494051947 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (239 + 1) - 1) % 2 ^ 256 = 2 ^ (239 + 1) - 1 by decide]
  rw [ray_eval_seam_239_lo]
  decide

private theorem wad_eval_seam_239_hi :
    model_ln_wad_to_wad_evm (2 ^ (239 + 1)) = 124908791660494051947 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (239 + 1)) % 2 ^ 256 = 2 ^ (239 + 1) by decide]
  rw [ray_eval_seam_239_hi]
  decide

private theorem ray_seam_239 :
    sle (model_ln_wad_evm (2 ^ (239 + 1) - 1)) (model_ln_wad_evm (2 ^ (239 + 1))) = true := by
  rw [ray_eval_seam_239_lo, ray_eval_seam_239_hi]
  unfold sle
  decide

private theorem wad_seam_239 :
    sle (model_ln_wad_to_wad_evm (2 ^ (239 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (239 + 1))) = true := by
  rw [wad_eval_seam_239_lo, wad_eval_seam_239_hi]
  unfold sle
  decide

private theorem ray_eval_seam_240_lo :
    model_ln_wad_evm (2 ^ (240 + 1) - 1) = 125601938841053997257229095086 := by
  have hlog : Nat.log2 (2 ^ (240 + 1) - 1) = 240 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (240 + 1) - 1) % 2 ^ 256 = 2 ^ (240 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_240_hi :
    model_ln_wad_evm (2 ^ (240 + 1)) = 125601938841053997257229095087 := by
  have hlog : Nat.log2 (2 ^ (240 + 1)) = 241 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (240 + 1)) % 2 ^ 256 = 2 ^ (240 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_240_lo :
    model_ln_wad_to_wad_evm (2 ^ (240 + 1) - 1) = 125601938841053997257 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (240 + 1) - 1) % 2 ^ 256 = 2 ^ (240 + 1) - 1 by decide]
  rw [ray_eval_seam_240_lo]
  decide

private theorem wad_eval_seam_240_hi :
    model_ln_wad_to_wad_evm (2 ^ (240 + 1)) = 125601938841053997257 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (240 + 1)) % 2 ^ 256 = 2 ^ (240 + 1) by decide]
  rw [ray_eval_seam_240_hi]
  decide

private theorem ray_seam_240 :
    sle (model_ln_wad_evm (2 ^ (240 + 1) - 1)) (model_ln_wad_evm (2 ^ (240 + 1))) = true := by
  rw [ray_eval_seam_240_lo, ray_eval_seam_240_hi]
  unfold sle
  decide

private theorem wad_seam_240 :
    sle (model_ln_wad_to_wad_evm (2 ^ (240 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (240 + 1))) = true := by
  rw [wad_eval_seam_240_lo, wad_eval_seam_240_hi]
  unfold sle
  decide

private theorem ray_eval_seam_241_lo :
    model_ln_wad_evm (2 ^ (241 + 1) - 1) = 126295086021613942566646327207 := by
  have hlog : Nat.log2 (2 ^ (241 + 1) - 1) = 241 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (241 + 1) - 1) % 2 ^ 256 = 2 ^ (241 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_241_hi :
    model_ln_wad_evm (2 ^ (241 + 1)) = 126295086021613942566646327208 := by
  have hlog : Nat.log2 (2 ^ (241 + 1)) = 242 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (241 + 1)) % 2 ^ 256 = 2 ^ (241 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_241_lo :
    model_ln_wad_to_wad_evm (2 ^ (241 + 1) - 1) = 126295086021613942566 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (241 + 1) - 1) % 2 ^ 256 = 2 ^ (241 + 1) - 1 by decide]
  rw [ray_eval_seam_241_lo]
  decide

private theorem wad_eval_seam_241_hi :
    model_ln_wad_to_wad_evm (2 ^ (241 + 1)) = 126295086021613942566 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (241 + 1)) % 2 ^ 256 = 2 ^ (241 + 1) by decide]
  rw [ray_eval_seam_241_hi]
  decide

private theorem ray_seam_241 :
    sle (model_ln_wad_evm (2 ^ (241 + 1) - 1)) (model_ln_wad_evm (2 ^ (241 + 1))) = true := by
  rw [ray_eval_seam_241_lo, ray_eval_seam_241_hi]
  unfold sle
  decide

private theorem wad_seam_241 :
    sle (model_ln_wad_to_wad_evm (2 ^ (241 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (241 + 1))) = true := by
  rw [wad_eval_seam_241_lo, wad_eval_seam_241_hi]
  unfold sle
  decide

private theorem ray_eval_seam_242_lo :
    model_ln_wad_evm (2 ^ (242 + 1) - 1) = 126988233202173887876063559329 := by
  have hlog : Nat.log2 (2 ^ (242 + 1) - 1) = 242 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (242 + 1) - 1) % 2 ^ 256 = 2 ^ (242 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_242_hi :
    model_ln_wad_evm (2 ^ (242 + 1)) = 126988233202173887876063559330 := by
  have hlog : Nat.log2 (2 ^ (242 + 1)) = 243 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (242 + 1)) % 2 ^ 256 = 2 ^ (242 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_242_lo :
    model_ln_wad_to_wad_evm (2 ^ (242 + 1) - 1) = 126988233202173887876 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (242 + 1) - 1) % 2 ^ 256 = 2 ^ (242 + 1) - 1 by decide]
  rw [ray_eval_seam_242_lo]
  decide

private theorem wad_eval_seam_242_hi :
    model_ln_wad_to_wad_evm (2 ^ (242 + 1)) = 126988233202173887876 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (242 + 1)) % 2 ^ 256 = 2 ^ (242 + 1) by decide]
  rw [ray_eval_seam_242_hi]
  decide

private theorem ray_seam_242 :
    sle (model_ln_wad_evm (2 ^ (242 + 1) - 1)) (model_ln_wad_evm (2 ^ (242 + 1))) = true := by
  rw [ray_eval_seam_242_lo, ray_eval_seam_242_hi]
  unfold sle
  decide

private theorem wad_seam_242 :
    sle (model_ln_wad_to_wad_evm (2 ^ (242 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (242 + 1))) = true := by
  rw [wad_eval_seam_242_lo, wad_eval_seam_242_hi]
  unfold sle
  decide

private theorem ray_eval_seam_243_lo :
    model_ln_wad_evm (2 ^ (243 + 1) - 1) = 127681380382733833185480791450 := by
  have hlog : Nat.log2 (2 ^ (243 + 1) - 1) = 243 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (243 + 1) - 1) % 2 ^ 256 = 2 ^ (243 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_243_hi :
    model_ln_wad_evm (2 ^ (243 + 1)) = 127681380382733833185480791451 := by
  have hlog : Nat.log2 (2 ^ (243 + 1)) = 244 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (243 + 1)) % 2 ^ 256 = 2 ^ (243 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_243_lo :
    model_ln_wad_to_wad_evm (2 ^ (243 + 1) - 1) = 127681380382733833185 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (243 + 1) - 1) % 2 ^ 256 = 2 ^ (243 + 1) - 1 by decide]
  rw [ray_eval_seam_243_lo]
  decide

private theorem wad_eval_seam_243_hi :
    model_ln_wad_to_wad_evm (2 ^ (243 + 1)) = 127681380382733833185 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (243 + 1)) % 2 ^ 256 = 2 ^ (243 + 1) by decide]
  rw [ray_eval_seam_243_hi]
  decide

private theorem ray_seam_243 :
    sle (model_ln_wad_evm (2 ^ (243 + 1) - 1)) (model_ln_wad_evm (2 ^ (243 + 1))) = true := by
  rw [ray_eval_seam_243_lo, ray_eval_seam_243_hi]
  unfold sle
  decide

private theorem wad_seam_243 :
    sle (model_ln_wad_to_wad_evm (2 ^ (243 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (243 + 1))) = true := by
  rw [wad_eval_seam_243_lo, wad_eval_seam_243_hi]
  unfold sle
  decide

private theorem ray_eval_seam_244_lo :
    model_ln_wad_evm (2 ^ (244 + 1) - 1) = 128374527563293778494898023572 := by
  have hlog : Nat.log2 (2 ^ (244 + 1) - 1) = 244 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (244 + 1) - 1) % 2 ^ 256 = 2 ^ (244 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_244_hi :
    model_ln_wad_evm (2 ^ (244 + 1)) = 128374527563293778494898023572 := by
  have hlog : Nat.log2 (2 ^ (244 + 1)) = 245 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (244 + 1)) % 2 ^ 256 = 2 ^ (244 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_244_lo :
    model_ln_wad_to_wad_evm (2 ^ (244 + 1) - 1) = 128374527563293778494 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (244 + 1) - 1) % 2 ^ 256 = 2 ^ (244 + 1) - 1 by decide]
  rw [ray_eval_seam_244_lo]
  decide

private theorem wad_eval_seam_244_hi :
    model_ln_wad_to_wad_evm (2 ^ (244 + 1)) = 128374527563293778494 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (244 + 1)) % 2 ^ 256 = 2 ^ (244 + 1) by decide]
  rw [ray_eval_seam_244_hi]
  decide

private theorem ray_seam_244 :
    sle (model_ln_wad_evm (2 ^ (244 + 1) - 1)) (model_ln_wad_evm (2 ^ (244 + 1))) = true := by
  rw [ray_eval_seam_244_lo, ray_eval_seam_244_hi]
  unfold sle
  decide

private theorem wad_seam_244 :
    sle (model_ln_wad_to_wad_evm (2 ^ (244 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (244 + 1))) = true := by
  rw [wad_eval_seam_244_lo, wad_eval_seam_244_hi]
  unfold sle
  decide

private theorem ray_eval_seam_245_lo :
    model_ln_wad_evm (2 ^ (245 + 1) - 1) = 129067674743853723804315255693 := by
  have hlog : Nat.log2 (2 ^ (245 + 1) - 1) = 245 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (245 + 1) - 1) % 2 ^ 256 = 2 ^ (245 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_245_hi :
    model_ln_wad_evm (2 ^ (245 + 1)) = 129067674743853723804315255694 := by
  have hlog : Nat.log2 (2 ^ (245 + 1)) = 246 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (245 + 1)) % 2 ^ 256 = 2 ^ (245 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_245_lo :
    model_ln_wad_to_wad_evm (2 ^ (245 + 1) - 1) = 129067674743853723804 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (245 + 1) - 1) % 2 ^ 256 = 2 ^ (245 + 1) - 1 by decide]
  rw [ray_eval_seam_245_lo]
  decide

private theorem wad_eval_seam_245_hi :
    model_ln_wad_to_wad_evm (2 ^ (245 + 1)) = 129067674743853723804 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (245 + 1)) % 2 ^ 256 = 2 ^ (245 + 1) by decide]
  rw [ray_eval_seam_245_hi]
  decide

private theorem ray_seam_245 :
    sle (model_ln_wad_evm (2 ^ (245 + 1) - 1)) (model_ln_wad_evm (2 ^ (245 + 1))) = true := by
  rw [ray_eval_seam_245_lo, ray_eval_seam_245_hi]
  unfold sle
  decide

private theorem wad_seam_245 :
    sle (model_ln_wad_to_wad_evm (2 ^ (245 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (245 + 1))) = true := by
  rw [wad_eval_seam_245_lo, wad_eval_seam_245_hi]
  unfold sle
  decide

private theorem ray_eval_seam_246_lo :
    model_ln_wad_evm (2 ^ (246 + 1) - 1) = 129760821924413669113732487815 := by
  have hlog : Nat.log2 (2 ^ (246 + 1) - 1) = 246 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (246 + 1) - 1) % 2 ^ 256 = 2 ^ (246 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_246_hi :
    model_ln_wad_evm (2 ^ (246 + 1)) = 129760821924413669113732487815 := by
  have hlog : Nat.log2 (2 ^ (246 + 1)) = 247 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (246 + 1)) % 2 ^ 256 = 2 ^ (246 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_246_lo :
    model_ln_wad_to_wad_evm (2 ^ (246 + 1) - 1) = 129760821924413669113 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (246 + 1) - 1) % 2 ^ 256 = 2 ^ (246 + 1) - 1 by decide]
  rw [ray_eval_seam_246_lo]
  decide

private theorem wad_eval_seam_246_hi :
    model_ln_wad_to_wad_evm (2 ^ (246 + 1)) = 129760821924413669113 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (246 + 1)) % 2 ^ 256 = 2 ^ (246 + 1) by decide]
  rw [ray_eval_seam_246_hi]
  decide

private theorem ray_seam_246 :
    sle (model_ln_wad_evm (2 ^ (246 + 1) - 1)) (model_ln_wad_evm (2 ^ (246 + 1))) = true := by
  rw [ray_eval_seam_246_lo, ray_eval_seam_246_hi]
  unfold sle
  decide

private theorem wad_seam_246 :
    sle (model_ln_wad_to_wad_evm (2 ^ (246 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (246 + 1))) = true := by
  rw [wad_eval_seam_246_lo, wad_eval_seam_246_hi]
  unfold sle
  decide

private theorem ray_eval_seam_247_lo :
    model_ln_wad_evm (2 ^ (247 + 1) - 1) = 130453969104973614423149719936 := by
  have hlog : Nat.log2 (2 ^ (247 + 1) - 1) = 247 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (247 + 1) - 1) % 2 ^ 256 = 2 ^ (247 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_247_hi :
    model_ln_wad_evm (2 ^ (247 + 1)) = 130453969104973614423149719937 := by
  have hlog : Nat.log2 (2 ^ (247 + 1)) = 248 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (247 + 1)) % 2 ^ 256 = 2 ^ (247 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_247_lo :
    model_ln_wad_to_wad_evm (2 ^ (247 + 1) - 1) = 130453969104973614423 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (247 + 1) - 1) % 2 ^ 256 = 2 ^ (247 + 1) - 1 by decide]
  rw [ray_eval_seam_247_lo]
  decide

private theorem wad_eval_seam_247_hi :
    model_ln_wad_to_wad_evm (2 ^ (247 + 1)) = 130453969104973614423 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (247 + 1)) % 2 ^ 256 = 2 ^ (247 + 1) by decide]
  rw [ray_eval_seam_247_hi]
  decide

private theorem ray_seam_247 :
    sle (model_ln_wad_evm (2 ^ (247 + 1) - 1)) (model_ln_wad_evm (2 ^ (247 + 1))) = true := by
  rw [ray_eval_seam_247_lo, ray_eval_seam_247_hi]
  unfold sle
  decide

private theorem wad_seam_247 :
    sle (model_ln_wad_to_wad_evm (2 ^ (247 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (247 + 1))) = true := by
  rw [wad_eval_seam_247_lo, wad_eval_seam_247_hi]
  unfold sle
  decide

private theorem ray_eval_seam_248_lo :
    model_ln_wad_evm (2 ^ (248 + 1) - 1) = 131147116285533559732566952058 := by
  have hlog : Nat.log2 (2 ^ (248 + 1) - 1) = 248 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (248 + 1) - 1) % 2 ^ 256 = 2 ^ (248 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_248_hi :
    model_ln_wad_evm (2 ^ (248 + 1)) = 131147116285533559732566952058 := by
  have hlog : Nat.log2 (2 ^ (248 + 1)) = 249 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (248 + 1)) % 2 ^ 256 = 2 ^ (248 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_248_lo :
    model_ln_wad_to_wad_evm (2 ^ (248 + 1) - 1) = 131147116285533559732 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (248 + 1) - 1) % 2 ^ 256 = 2 ^ (248 + 1) - 1 by decide]
  rw [ray_eval_seam_248_lo]
  decide

private theorem wad_eval_seam_248_hi :
    model_ln_wad_to_wad_evm (2 ^ (248 + 1)) = 131147116285533559732 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (248 + 1)) % 2 ^ 256 = 2 ^ (248 + 1) by decide]
  rw [ray_eval_seam_248_hi]
  decide

private theorem ray_seam_248 :
    sle (model_ln_wad_evm (2 ^ (248 + 1) - 1)) (model_ln_wad_evm (2 ^ (248 + 1))) = true := by
  rw [ray_eval_seam_248_lo, ray_eval_seam_248_hi]
  unfold sle
  decide

private theorem wad_seam_248 :
    sle (model_ln_wad_to_wad_evm (2 ^ (248 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (248 + 1))) = true := by
  rw [wad_eval_seam_248_lo, wad_eval_seam_248_hi]
  unfold sle
  decide

private theorem ray_eval_seam_249_lo :
    model_ln_wad_evm (2 ^ (249 + 1) - 1) = 131840263466093505041984184179 := by
  have hlog : Nat.log2 (2 ^ (249 + 1) - 1) = 249 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (249 + 1) - 1) % 2 ^ 256 = 2 ^ (249 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_249_hi :
    model_ln_wad_evm (2 ^ (249 + 1)) = 131840263466093505041984184180 := by
  have hlog : Nat.log2 (2 ^ (249 + 1)) = 250 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (249 + 1)) % 2 ^ 256 = 2 ^ (249 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_249_lo :
    model_ln_wad_to_wad_evm (2 ^ (249 + 1) - 1) = 131840263466093505041 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (249 + 1) - 1) % 2 ^ 256 = 2 ^ (249 + 1) - 1 by decide]
  rw [ray_eval_seam_249_lo]
  decide

private theorem wad_eval_seam_249_hi :
    model_ln_wad_to_wad_evm (2 ^ (249 + 1)) = 131840263466093505041 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (249 + 1)) % 2 ^ 256 = 2 ^ (249 + 1) by decide]
  rw [ray_eval_seam_249_hi]
  decide

private theorem ray_seam_249 :
    sle (model_ln_wad_evm (2 ^ (249 + 1) - 1)) (model_ln_wad_evm (2 ^ (249 + 1))) = true := by
  rw [ray_eval_seam_249_lo, ray_eval_seam_249_hi]
  unfold sle
  decide

private theorem wad_seam_249 :
    sle (model_ln_wad_to_wad_evm (2 ^ (249 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (249 + 1))) = true := by
  rw [wad_eval_seam_249_lo, wad_eval_seam_249_hi]
  unfold sle
  decide

private theorem ray_eval_seam_250_lo :
    model_ln_wad_evm (2 ^ (250 + 1) - 1) = 132533410646653450351401416301 := by
  have hlog : Nat.log2 (2 ^ (250 + 1) - 1) = 250 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (250 + 1) - 1) % 2 ^ 256 = 2 ^ (250 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_250_hi :
    model_ln_wad_evm (2 ^ (250 + 1)) = 132533410646653450351401416301 := by
  have hlog : Nat.log2 (2 ^ (250 + 1)) = 251 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (250 + 1)) % 2 ^ 256 = 2 ^ (250 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_250_lo :
    model_ln_wad_to_wad_evm (2 ^ (250 + 1) - 1) = 132533410646653450351 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (250 + 1) - 1) % 2 ^ 256 = 2 ^ (250 + 1) - 1 by decide]
  rw [ray_eval_seam_250_lo]
  decide

private theorem wad_eval_seam_250_hi :
    model_ln_wad_to_wad_evm (2 ^ (250 + 1)) = 132533410646653450351 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (250 + 1)) % 2 ^ 256 = 2 ^ (250 + 1) by decide]
  rw [ray_eval_seam_250_hi]
  decide

private theorem ray_seam_250 :
    sle (model_ln_wad_evm (2 ^ (250 + 1) - 1)) (model_ln_wad_evm (2 ^ (250 + 1))) = true := by
  rw [ray_eval_seam_250_lo, ray_eval_seam_250_hi]
  unfold sle
  decide

private theorem wad_seam_250 :
    sle (model_ln_wad_to_wad_evm (2 ^ (250 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (250 + 1))) = true := by
  rw [wad_eval_seam_250_lo, wad_eval_seam_250_hi]
  unfold sle
  decide

private theorem ray_eval_seam_251_lo :
    model_ln_wad_evm (2 ^ (251 + 1) - 1) = 133226557827213395660818648422 := by
  have hlog : Nat.log2 (2 ^ (251 + 1) - 1) = 251 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (251 + 1) - 1) % 2 ^ 256 = 2 ^ (251 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_251_hi :
    model_ln_wad_evm (2 ^ (251 + 1)) = 133226557827213395660818648423 := by
  have hlog : Nat.log2 (2 ^ (251 + 1)) = 252 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (251 + 1)) % 2 ^ 256 = 2 ^ (251 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_251_lo :
    model_ln_wad_to_wad_evm (2 ^ (251 + 1) - 1) = 133226557827213395660 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (251 + 1) - 1) % 2 ^ 256 = 2 ^ (251 + 1) - 1 by decide]
  rw [ray_eval_seam_251_lo]
  decide

private theorem wad_eval_seam_251_hi :
    model_ln_wad_to_wad_evm (2 ^ (251 + 1)) = 133226557827213395660 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (251 + 1)) % 2 ^ 256 = 2 ^ (251 + 1) by decide]
  rw [ray_eval_seam_251_hi]
  decide

private theorem ray_seam_251 :
    sle (model_ln_wad_evm (2 ^ (251 + 1) - 1)) (model_ln_wad_evm (2 ^ (251 + 1))) = true := by
  rw [ray_eval_seam_251_lo, ray_eval_seam_251_hi]
  unfold sle
  decide

private theorem wad_seam_251 :
    sle (model_ln_wad_to_wad_evm (2 ^ (251 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (251 + 1))) = true := by
  rw [wad_eval_seam_251_lo, wad_eval_seam_251_hi]
  unfold sle
  decide

private theorem ray_eval_seam_252_lo :
    model_ln_wad_evm (2 ^ (252 + 1) - 1) = 133919705007773340970235880543 := by
  have hlog : Nat.log2 (2 ^ (252 + 1) - 1) = 252 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (252 + 1) - 1) % 2 ^ 256 = 2 ^ (252 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_252_hi :
    model_ln_wad_evm (2 ^ (252 + 1)) = 133919705007773340970235880544 := by
  have hlog : Nat.log2 (2 ^ (252 + 1)) = 253 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (252 + 1)) % 2 ^ 256 = 2 ^ (252 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_252_lo :
    model_ln_wad_to_wad_evm (2 ^ (252 + 1) - 1) = 133919705007773340970 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (252 + 1) - 1) % 2 ^ 256 = 2 ^ (252 + 1) - 1 by decide]
  rw [ray_eval_seam_252_lo]
  decide

private theorem wad_eval_seam_252_hi :
    model_ln_wad_to_wad_evm (2 ^ (252 + 1)) = 133919705007773340970 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (252 + 1)) % 2 ^ 256 = 2 ^ (252 + 1) by decide]
  rw [ray_eval_seam_252_hi]
  decide

private theorem ray_seam_252 :
    sle (model_ln_wad_evm (2 ^ (252 + 1) - 1)) (model_ln_wad_evm (2 ^ (252 + 1))) = true := by
  rw [ray_eval_seam_252_lo, ray_eval_seam_252_hi]
  unfold sle
  decide

private theorem wad_seam_252 :
    sle (model_ln_wad_to_wad_evm (2 ^ (252 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (252 + 1))) = true := by
  rw [wad_eval_seam_252_lo, wad_eval_seam_252_hi]
  unfold sle
  decide

private theorem ray_eval_seam_253_lo :
    model_ln_wad_evm (2 ^ (253 + 1) - 1) = 134612852188333286279653112665 := by
  have hlog : Nat.log2 (2 ^ (253 + 1) - 1) = 253 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (253 + 1) - 1) % 2 ^ 256 = 2 ^ (253 + 1) - 1 by decide]
  simp only [hlog]
  decide

private theorem ray_eval_seam_253_hi :
    model_ln_wad_evm (2 ^ (253 + 1)) = 134612852188333286279653112666 := by
  have hlog : Nat.log2 (2 ^ (253 + 1)) = 254 := by
    rw [log2_eq_iff] <;> decide
  unfold model_ln_wad_evm evmClz
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (253 + 1)) % 2 ^ 256 = 2 ^ (253 + 1) by decide]
  simp only [hlog]
  decide

private theorem wad_eval_seam_253_lo :
    model_ln_wad_to_wad_evm (2 ^ (253 + 1) - 1) = 134612852188333286279 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (253 + 1) - 1) % 2 ^ 256 = 2 ^ (253 + 1) - 1 by decide]
  rw [ray_eval_seam_253_lo]
  decide

private theorem wad_eval_seam_253_hi :
    model_ln_wad_to_wad_evm (2 ^ (253 + 1)) = 134612852188333286279 := by
  unfold model_ln_wad_to_wad_evm
  simp only [u256, WORD_MOD]
  simp only [show (2 ^ (253 + 1)) % 2 ^ 256 = 2 ^ (253 + 1) by decide]
  rw [ray_eval_seam_253_hi]
  decide

private theorem ray_seam_253 :
    sle (model_ln_wad_evm (2 ^ (253 + 1) - 1)) (model_ln_wad_evm (2 ^ (253 + 1))) = true := by
  rw [ray_eval_seam_253_lo, ray_eval_seam_253_hi]
  unfold sle
  decide

private theorem wad_seam_253 :
    sle (model_ln_wad_to_wad_evm (2 ^ (253 + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (253 + 1))) = true := by
  rw [wad_eval_seam_253_lo, wad_eval_seam_253_hi]
  unfold sle
  decide

private theorem ray_seam_at (t : Nat) (ht : t < 254) :
    sle (model_ln_wad_evm (2 ^ (t + 1) - 1)) (model_ln_wad_evm (2 ^ (t + 1))) = true := by
  match t with
  | 0 => exact ray_seam_0
  | 1 => exact ray_seam_1
  | 2 => exact ray_seam_2
  | 3 => exact ray_seam_3
  | 4 => exact ray_seam_4
  | 5 => exact ray_seam_5
  | 6 => exact ray_seam_6
  | 7 => exact ray_seam_7
  | 8 => exact ray_seam_8
  | 9 => exact ray_seam_9
  | 10 => exact ray_seam_10
  | 11 => exact ray_seam_11
  | 12 => exact ray_seam_12
  | 13 => exact ray_seam_13
  | 14 => exact ray_seam_14
  | 15 => exact ray_seam_15
  | 16 => exact ray_seam_16
  | 17 => exact ray_seam_17
  | 18 => exact ray_seam_18
  | 19 => exact ray_seam_19
  | 20 => exact ray_seam_20
  | 21 => exact ray_seam_21
  | 22 => exact ray_seam_22
  | 23 => exact ray_seam_23
  | 24 => exact ray_seam_24
  | 25 => exact ray_seam_25
  | 26 => exact ray_seam_26
  | 27 => exact ray_seam_27
  | 28 => exact ray_seam_28
  | 29 => exact ray_seam_29
  | 30 => exact ray_seam_30
  | 31 => exact ray_seam_31
  | 32 => exact ray_seam_32
  | 33 => exact ray_seam_33
  | 34 => exact ray_seam_34
  | 35 => exact ray_seam_35
  | 36 => exact ray_seam_36
  | 37 => exact ray_seam_37
  | 38 => exact ray_seam_38
  | 39 => exact ray_seam_39
  | 40 => exact ray_seam_40
  | 41 => exact ray_seam_41
  | 42 => exact ray_seam_42
  | 43 => exact ray_seam_43
  | 44 => exact ray_seam_44
  | 45 => exact ray_seam_45
  | 46 => exact ray_seam_46
  | 47 => exact ray_seam_47
  | 48 => exact ray_seam_48
  | 49 => exact ray_seam_49
  | 50 => exact ray_seam_50
  | 51 => exact ray_seam_51
  | 52 => exact ray_seam_52
  | 53 => exact ray_seam_53
  | 54 => exact ray_seam_54
  | 55 => exact ray_seam_55
  | 56 => exact ray_seam_56
  | 57 => exact ray_seam_57
  | 58 => exact ray_seam_58
  | 59 => exact ray_seam_59
  | 60 => exact ray_seam_60
  | 61 => exact ray_seam_61
  | 62 => exact ray_seam_62
  | 63 => exact ray_seam_63
  | 64 => exact ray_seam_64
  | 65 => exact ray_seam_65
  | 66 => exact ray_seam_66
  | 67 => exact ray_seam_67
  | 68 => exact ray_seam_68
  | 69 => exact ray_seam_69
  | 70 => exact ray_seam_70
  | 71 => exact ray_seam_71
  | 72 => exact ray_seam_72
  | 73 => exact ray_seam_73
  | 74 => exact ray_seam_74
  | 75 => exact ray_seam_75
  | 76 => exact ray_seam_76
  | 77 => exact ray_seam_77
  | 78 => exact ray_seam_78
  | 79 => exact ray_seam_79
  | 80 => exact ray_seam_80
  | 81 => exact ray_seam_81
  | 82 => exact ray_seam_82
  | 83 => exact ray_seam_83
  | 84 => exact ray_seam_84
  | 85 => exact ray_seam_85
  | 86 => exact ray_seam_86
  | 87 => exact ray_seam_87
  | 88 => exact ray_seam_88
  | 89 => exact ray_seam_89
  | 90 => exact ray_seam_90
  | 91 => exact ray_seam_91
  | 92 => exact ray_seam_92
  | 93 => exact ray_seam_93
  | 94 => exact ray_seam_94
  | 95 => exact ray_seam_95
  | 96 => exact ray_seam_96
  | 97 => exact ray_seam_97
  | 98 => exact ray_seam_98
  | 99 => exact ray_seam_99
  | 100 => exact ray_seam_100
  | 101 => exact ray_seam_101
  | 102 => exact ray_seam_102
  | 103 => exact ray_seam_103
  | 104 => exact ray_seam_104
  | 105 => exact ray_seam_105
  | 106 => exact ray_seam_106
  | 107 => exact ray_seam_107
  | 108 => exact ray_seam_108
  | 109 => exact ray_seam_109
  | 110 => exact ray_seam_110
  | 111 => exact ray_seam_111
  | 112 => exact ray_seam_112
  | 113 => exact ray_seam_113
  | 114 => exact ray_seam_114
  | 115 => exact ray_seam_115
  | 116 => exact ray_seam_116
  | 117 => exact ray_seam_117
  | 118 => exact ray_seam_118
  | 119 => exact ray_seam_119
  | 120 => exact ray_seam_120
  | 121 => exact ray_seam_121
  | 122 => exact ray_seam_122
  | 123 => exact ray_seam_123
  | 124 => exact ray_seam_124
  | 125 => exact ray_seam_125
  | 126 => exact ray_seam_126
  | 127 => exact ray_seam_127
  | 128 => exact ray_seam_128
  | 129 => exact ray_seam_129
  | 130 => exact ray_seam_130
  | 131 => exact ray_seam_131
  | 132 => exact ray_seam_132
  | 133 => exact ray_seam_133
  | 134 => exact ray_seam_134
  | 135 => exact ray_seam_135
  | 136 => exact ray_seam_136
  | 137 => exact ray_seam_137
  | 138 => exact ray_seam_138
  | 139 => exact ray_seam_139
  | 140 => exact ray_seam_140
  | 141 => exact ray_seam_141
  | 142 => exact ray_seam_142
  | 143 => exact ray_seam_143
  | 144 => exact ray_seam_144
  | 145 => exact ray_seam_145
  | 146 => exact ray_seam_146
  | 147 => exact ray_seam_147
  | 148 => exact ray_seam_148
  | 149 => exact ray_seam_149
  | 150 => exact ray_seam_150
  | 151 => exact ray_seam_151
  | 152 => exact ray_seam_152
  | 153 => exact ray_seam_153
  | 154 => exact ray_seam_154
  | 155 => exact ray_seam_155
  | 156 => exact ray_seam_156
  | 157 => exact ray_seam_157
  | 158 => exact ray_seam_158
  | 159 => exact ray_seam_159
  | 160 => exact ray_seam_160
  | 161 => exact ray_seam_161
  | 162 => exact ray_seam_162
  | 163 => exact ray_seam_163
  | 164 => exact ray_seam_164
  | 165 => exact ray_seam_165
  | 166 => exact ray_seam_166
  | 167 => exact ray_seam_167
  | 168 => exact ray_seam_168
  | 169 => exact ray_seam_169
  | 170 => exact ray_seam_170
  | 171 => exact ray_seam_171
  | 172 => exact ray_seam_172
  | 173 => exact ray_seam_173
  | 174 => exact ray_seam_174
  | 175 => exact ray_seam_175
  | 176 => exact ray_seam_176
  | 177 => exact ray_seam_177
  | 178 => exact ray_seam_178
  | 179 => exact ray_seam_179
  | 180 => exact ray_seam_180
  | 181 => exact ray_seam_181
  | 182 => exact ray_seam_182
  | 183 => exact ray_seam_183
  | 184 => exact ray_seam_184
  | 185 => exact ray_seam_185
  | 186 => exact ray_seam_186
  | 187 => exact ray_seam_187
  | 188 => exact ray_seam_188
  | 189 => exact ray_seam_189
  | 190 => exact ray_seam_190
  | 191 => exact ray_seam_191
  | 192 => exact ray_seam_192
  | 193 => exact ray_seam_193
  | 194 => exact ray_seam_194
  | 195 => exact ray_seam_195
  | 196 => exact ray_seam_196
  | 197 => exact ray_seam_197
  | 198 => exact ray_seam_198
  | 199 => exact ray_seam_199
  | 200 => exact ray_seam_200
  | 201 => exact ray_seam_201
  | 202 => exact ray_seam_202
  | 203 => exact ray_seam_203
  | 204 => exact ray_seam_204
  | 205 => exact ray_seam_205
  | 206 => exact ray_seam_206
  | 207 => exact ray_seam_207
  | 208 => exact ray_seam_208
  | 209 => exact ray_seam_209
  | 210 => exact ray_seam_210
  | 211 => exact ray_seam_211
  | 212 => exact ray_seam_212
  | 213 => exact ray_seam_213
  | 214 => exact ray_seam_214
  | 215 => exact ray_seam_215
  | 216 => exact ray_seam_216
  | 217 => exact ray_seam_217
  | 218 => exact ray_seam_218
  | 219 => exact ray_seam_219
  | 220 => exact ray_seam_220
  | 221 => exact ray_seam_221
  | 222 => exact ray_seam_222
  | 223 => exact ray_seam_223
  | 224 => exact ray_seam_224
  | 225 => exact ray_seam_225
  | 226 => exact ray_seam_226
  | 227 => exact ray_seam_227
  | 228 => exact ray_seam_228
  | 229 => exact ray_seam_229
  | 230 => exact ray_seam_230
  | 231 => exact ray_seam_231
  | 232 => exact ray_seam_232
  | 233 => exact ray_seam_233
  | 234 => exact ray_seam_234
  | 235 => exact ray_seam_235
  | 236 => exact ray_seam_236
  | 237 => exact ray_seam_237
  | 238 => exact ray_seam_238
  | 239 => exact ray_seam_239
  | 240 => exact ray_seam_240
  | 241 => exact ray_seam_241
  | 242 => exact ray_seam_242
  | 243 => exact ray_seam_243
  | 244 => exact ray_seam_244
  | 245 => exact ray_seam_245
  | 246 => exact ray_seam_246
  | 247 => exact ray_seam_247
  | 248 => exact ray_seam_248
  | 249 => exact ray_seam_249
  | 250 => exact ray_seam_250
  | 251 => exact ray_seam_251
  | 252 => exact ray_seam_252
  | 253 => exact ray_seam_253
  | n + 254 => omega

private theorem wad_seam_at (t : Nat) (ht : t < 254) :
    sle (model_ln_wad_to_wad_evm (2 ^ (t + 1) - 1)) (model_ln_wad_to_wad_evm (2 ^ (t + 1))) = true := by
  match t with
  | 0 => exact wad_seam_0
  | 1 => exact wad_seam_1
  | 2 => exact wad_seam_2
  | 3 => exact wad_seam_3
  | 4 => exact wad_seam_4
  | 5 => exact wad_seam_5
  | 6 => exact wad_seam_6
  | 7 => exact wad_seam_7
  | 8 => exact wad_seam_8
  | 9 => exact wad_seam_9
  | 10 => exact wad_seam_10
  | 11 => exact wad_seam_11
  | 12 => exact wad_seam_12
  | 13 => exact wad_seam_13
  | 14 => exact wad_seam_14
  | 15 => exact wad_seam_15
  | 16 => exact wad_seam_16
  | 17 => exact wad_seam_17
  | 18 => exact wad_seam_18
  | 19 => exact wad_seam_19
  | 20 => exact wad_seam_20
  | 21 => exact wad_seam_21
  | 22 => exact wad_seam_22
  | 23 => exact wad_seam_23
  | 24 => exact wad_seam_24
  | 25 => exact wad_seam_25
  | 26 => exact wad_seam_26
  | 27 => exact wad_seam_27
  | 28 => exact wad_seam_28
  | 29 => exact wad_seam_29
  | 30 => exact wad_seam_30
  | 31 => exact wad_seam_31
  | 32 => exact wad_seam_32
  | 33 => exact wad_seam_33
  | 34 => exact wad_seam_34
  | 35 => exact wad_seam_35
  | 36 => exact wad_seam_36
  | 37 => exact wad_seam_37
  | 38 => exact wad_seam_38
  | 39 => exact wad_seam_39
  | 40 => exact wad_seam_40
  | 41 => exact wad_seam_41
  | 42 => exact wad_seam_42
  | 43 => exact wad_seam_43
  | 44 => exact wad_seam_44
  | 45 => exact wad_seam_45
  | 46 => exact wad_seam_46
  | 47 => exact wad_seam_47
  | 48 => exact wad_seam_48
  | 49 => exact wad_seam_49
  | 50 => exact wad_seam_50
  | 51 => exact wad_seam_51
  | 52 => exact wad_seam_52
  | 53 => exact wad_seam_53
  | 54 => exact wad_seam_54
  | 55 => exact wad_seam_55
  | 56 => exact wad_seam_56
  | 57 => exact wad_seam_57
  | 58 => exact wad_seam_58
  | 59 => exact wad_seam_59
  | 60 => exact wad_seam_60
  | 61 => exact wad_seam_61
  | 62 => exact wad_seam_62
  | 63 => exact wad_seam_63
  | 64 => exact wad_seam_64
  | 65 => exact wad_seam_65
  | 66 => exact wad_seam_66
  | 67 => exact wad_seam_67
  | 68 => exact wad_seam_68
  | 69 => exact wad_seam_69
  | 70 => exact wad_seam_70
  | 71 => exact wad_seam_71
  | 72 => exact wad_seam_72
  | 73 => exact wad_seam_73
  | 74 => exact wad_seam_74
  | 75 => exact wad_seam_75
  | 76 => exact wad_seam_76
  | 77 => exact wad_seam_77
  | 78 => exact wad_seam_78
  | 79 => exact wad_seam_79
  | 80 => exact wad_seam_80
  | 81 => exact wad_seam_81
  | 82 => exact wad_seam_82
  | 83 => exact wad_seam_83
  | 84 => exact wad_seam_84
  | 85 => exact wad_seam_85
  | 86 => exact wad_seam_86
  | 87 => exact wad_seam_87
  | 88 => exact wad_seam_88
  | 89 => exact wad_seam_89
  | 90 => exact wad_seam_90
  | 91 => exact wad_seam_91
  | 92 => exact wad_seam_92
  | 93 => exact wad_seam_93
  | 94 => exact wad_seam_94
  | 95 => exact wad_seam_95
  | 96 => exact wad_seam_96
  | 97 => exact wad_seam_97
  | 98 => exact wad_seam_98
  | 99 => exact wad_seam_99
  | 100 => exact wad_seam_100
  | 101 => exact wad_seam_101
  | 102 => exact wad_seam_102
  | 103 => exact wad_seam_103
  | 104 => exact wad_seam_104
  | 105 => exact wad_seam_105
  | 106 => exact wad_seam_106
  | 107 => exact wad_seam_107
  | 108 => exact wad_seam_108
  | 109 => exact wad_seam_109
  | 110 => exact wad_seam_110
  | 111 => exact wad_seam_111
  | 112 => exact wad_seam_112
  | 113 => exact wad_seam_113
  | 114 => exact wad_seam_114
  | 115 => exact wad_seam_115
  | 116 => exact wad_seam_116
  | 117 => exact wad_seam_117
  | 118 => exact wad_seam_118
  | 119 => exact wad_seam_119
  | 120 => exact wad_seam_120
  | 121 => exact wad_seam_121
  | 122 => exact wad_seam_122
  | 123 => exact wad_seam_123
  | 124 => exact wad_seam_124
  | 125 => exact wad_seam_125
  | 126 => exact wad_seam_126
  | 127 => exact wad_seam_127
  | 128 => exact wad_seam_128
  | 129 => exact wad_seam_129
  | 130 => exact wad_seam_130
  | 131 => exact wad_seam_131
  | 132 => exact wad_seam_132
  | 133 => exact wad_seam_133
  | 134 => exact wad_seam_134
  | 135 => exact wad_seam_135
  | 136 => exact wad_seam_136
  | 137 => exact wad_seam_137
  | 138 => exact wad_seam_138
  | 139 => exact wad_seam_139
  | 140 => exact wad_seam_140
  | 141 => exact wad_seam_141
  | 142 => exact wad_seam_142
  | 143 => exact wad_seam_143
  | 144 => exact wad_seam_144
  | 145 => exact wad_seam_145
  | 146 => exact wad_seam_146
  | 147 => exact wad_seam_147
  | 148 => exact wad_seam_148
  | 149 => exact wad_seam_149
  | 150 => exact wad_seam_150
  | 151 => exact wad_seam_151
  | 152 => exact wad_seam_152
  | 153 => exact wad_seam_153
  | 154 => exact wad_seam_154
  | 155 => exact wad_seam_155
  | 156 => exact wad_seam_156
  | 157 => exact wad_seam_157
  | 158 => exact wad_seam_158
  | 159 => exact wad_seam_159
  | 160 => exact wad_seam_160
  | 161 => exact wad_seam_161
  | 162 => exact wad_seam_162
  | 163 => exact wad_seam_163
  | 164 => exact wad_seam_164
  | 165 => exact wad_seam_165
  | 166 => exact wad_seam_166
  | 167 => exact wad_seam_167
  | 168 => exact wad_seam_168
  | 169 => exact wad_seam_169
  | 170 => exact wad_seam_170
  | 171 => exact wad_seam_171
  | 172 => exact wad_seam_172
  | 173 => exact wad_seam_173
  | 174 => exact wad_seam_174
  | 175 => exact wad_seam_175
  | 176 => exact wad_seam_176
  | 177 => exact wad_seam_177
  | 178 => exact wad_seam_178
  | 179 => exact wad_seam_179
  | 180 => exact wad_seam_180
  | 181 => exact wad_seam_181
  | 182 => exact wad_seam_182
  | 183 => exact wad_seam_183
  | 184 => exact wad_seam_184
  | 185 => exact wad_seam_185
  | 186 => exact wad_seam_186
  | 187 => exact wad_seam_187
  | 188 => exact wad_seam_188
  | 189 => exact wad_seam_189
  | 190 => exact wad_seam_190
  | 191 => exact wad_seam_191
  | 192 => exact wad_seam_192
  | 193 => exact wad_seam_193
  | 194 => exact wad_seam_194
  | 195 => exact wad_seam_195
  | 196 => exact wad_seam_196
  | 197 => exact wad_seam_197
  | 198 => exact wad_seam_198
  | 199 => exact wad_seam_199
  | 200 => exact wad_seam_200
  | 201 => exact wad_seam_201
  | 202 => exact wad_seam_202
  | 203 => exact wad_seam_203
  | 204 => exact wad_seam_204
  | 205 => exact wad_seam_205
  | 206 => exact wad_seam_206
  | 207 => exact wad_seam_207
  | 208 => exact wad_seam_208
  | 209 => exact wad_seam_209
  | 210 => exact wad_seam_210
  | 211 => exact wad_seam_211
  | 212 => exact wad_seam_212
  | 213 => exact wad_seam_213
  | 214 => exact wad_seam_214
  | 215 => exact wad_seam_215
  | 216 => exact wad_seam_216
  | 217 => exact wad_seam_217
  | 218 => exact wad_seam_218
  | 219 => exact wad_seam_219
  | 220 => exact wad_seam_220
  | 221 => exact wad_seam_221
  | 222 => exact wad_seam_222
  | 223 => exact wad_seam_223
  | 224 => exact wad_seam_224
  | 225 => exact wad_seam_225
  | 226 => exact wad_seam_226
  | 227 => exact wad_seam_227
  | 228 => exact wad_seam_228
  | 229 => exact wad_seam_229
  | 230 => exact wad_seam_230
  | 231 => exact wad_seam_231
  | 232 => exact wad_seam_232
  | 233 => exact wad_seam_233
  | 234 => exact wad_seam_234
  | 235 => exact wad_seam_235
  | 236 => exact wad_seam_236
  | 237 => exact wad_seam_237
  | 238 => exact wad_seam_238
  | 239 => exact wad_seam_239
  | 240 => exact wad_seam_240
  | 241 => exact wad_seam_241
  | 242 => exact wad_seam_242
  | 243 => exact wad_seam_243
  | 244 => exact wad_seam_244
  | 245 => exact wad_seam_245
  | 246 => exact wad_seam_246
  | 247 => exact wad_seam_247
  | 248 => exact wad_seam_248
  | 249 => exact wad_seam_249
  | 250 => exact wad_seam_250
  | 251 => exact wad_seam_251
  | 252 => exact wad_seam_252
  | 253 => exact wad_seam_253
  | n + 254 => omega

/-- `lnWad` is monotone across every clz seam. -/
theorem model_ln_wad_seam_mono : seamMono model_ln_wad_evm = true := by
  rw [seamMono, List.all_eq_true]
  intro t ht
  exact ray_seam_at t (List.mem_range.mp ht)

/-- `lnWadToWad` is monotone across every clz seam. -/
theorem model_ln_wad_to_wad_seam_mono : seamMono model_ln_wad_to_wad_evm = true := by
  rw [seamMono, List.all_eq_true]
  intro t ht
  exact wad_seam_at t (List.mem_range.mp ht)

end LnYul
