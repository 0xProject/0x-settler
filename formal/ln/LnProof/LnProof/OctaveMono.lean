import LnProof.ZOctave

/-!
# Within-octave monotonicity of the model tail

`lnTail one kw m` is the generated model's pipeline downstream of the
`(eq, clz-exponent, mantissa)` triple. `model_eq_tail` re-expresses the
generated model through it, `ln2k_bound` brackets the `ln2 * k` term by
kernel evaluation over all 256 `clz` values, and `tail_mono` pushes
`r1_mono` through the fixed-exponent affine tail.
-/

set_option maxRecDepth 4096

namespace LnGeneratedModel

open LnPoly

/-- The model tail downstream of `(one, k, mantissa)`. -/
def lnTail (one kw m : Nat) : Nat :=
  evmAdd
    (evmSar 72
      (evmAdd (evmAdd (evmMul (x1W (zWord m)) Kc) (evmMul LN2c kw)) BIASc))
    one

/-- `mul`, `add`, and `eq` are commutative on words. The generated model writes
their constant operands first (`mul(K, r)`, `add(BIAS, r)`, `eq(10**18, x)`);
these orient those occurrences to the constant-second form `lnTail` uses. -/
theorem evmMul_comm (a b : Nat) : evmMul a b = evmMul b a := by
  unfold evmMul; rw [Nat.mul_comm (u256 a) (u256 b)]

theorem evmAdd_comm (a b : Nat) : evmAdd a b = evmAdd b a := by
  unfold evmAdd; rw [Nat.add_comm (u256 a) (u256 b)]

theorem evmEq_comm (a b : Nat) : evmEq a b = evmEq b a := by
  unfold evmEq
  by_cases h : u256 a = u256 b
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg fun he => h he.symm]

theorem model_eq_tail {x : Nat} (h : x < 2 ^ 256) :
    model_ln_wad_evm x =
      lnTail (evmEq x 1000000000000000000) (evmSub 160 (evmClz x))
        (evmShr 160 (evmShl (evmClz x) x)) := by
  unfold model_ln_wad_evm lnTail x1W pS4 pS3 pS2 pS1 qS5 qS4 qS3 qS2 qS1 uWord zWord
  simp only [Sc, P4c, P3c, P2c, P1c, C0c, Q4c, Q3c, Q2c, Q1c, Kc, LN2c, BIASc,
    u256_of_lt h]
  rw [evmEq_comm 1000000000000000000 x, evmMul_comm 7450580596923828125,
    evmAdd_comm (evmMul 3273295013171879848905889459134067659407864468560
      (evmSub 160 (evmClz x))),
    evmAdd_comm 116873961749927929127912020551506849476088469858172]

/-- Per-`clz` bracket on the signed value of `ln2 * k`; `[-LN2c*95, LN2c*160]`. -/
def ln2kOK (c : Nat) : Bool :=
  decide (-(310963026251328585646059498617736427643747124513200 : Int) ≤
      toInt (evmMul LN2c (evmSub 160 c)) ∧
    toInt (evmMul LN2c (evmSub 160 c)) ≤
      (523727202107500775824942313461450825505258314969600 : Int))

theorem ln2k_all : (List.range 256).all ln2kOK = true := by decide

theorem ln2k_bound {c : Nat} (hc : c < 256) :
    -(310963026251328585646059498617736427643747124513200 : Int) ≤
        toInt (evmMul LN2c (evmSub 160 c)) ∧
      toInt (evmMul LN2c (evmSub 160 c)) ≤
        (523727202107500775824942313461450825505258314969600 : Int) := by
  have h := ln2k_all
  rw [List.all_eq_true] at h
  have hm := h c (List.mem_range.mpr hc)
  rw [ln2kOK, decide_eq_true_eq] at hm
  exact hm

theorem evmAdd_zero {a : Nat} (h : a < 2 ^ 256) : evmAdd a 0 = a := by
  unfold evmAdd u256
  simp only [word_mod_eq]
  omega

/-- Affine tail over abstract words: `sar72(a*K + W + BIAS) (+ 0)` is
monotone in the signed value of `a` when every leaf is bracketed. -/
theorem affine_tail_mono {a a' W : Nat}
    (haw : a < 2 ^ 256) (haw' : a' < 2 ^ 256) (hWw : W < 2 ^ 256)
    (hA : toInt a ≤ toInt a')
    (hBa1 : -(240000000000000000000000000000 : Int) ≤ toInt a)
    (hBa2 : toInt a ≤ (240000000000000000000000000000 : Int))
    (hBa1' : -(240000000000000000000000000000 : Int) ≤ toInt a')
    (hBa2' : toInt a' ≤ (240000000000000000000000000000 : Int))
    (hW1 : -(310963026251328585646059498617736427643747124513200 : Int) ≤ toInt W)
    (hW2 : toInt W ≤ (523727202107500775824942313461450825505258314969600 : Int)) :
    toInt (evmAdd (evmSar 72 (evmAdd (evmAdd (evmMul a Kc) W) BIASc)) 0) ≤
      toInt (evmAdd (evmSar 72 (evmAdd (evmAdd (evmMul a' Kc) W) BIASc)) 0) := by
  have hKlt : Kc < 2 ^ 256 := by simp only [Kc]; omega
  have hKc : toInt Kc = (7450580596923828125 : Int) := by
    rw [toInt_of_lt (by simp only [Kc]; omega)]
    simp only [Kc]
    omega
  have e2 : toInt (evmMul a Kc) = toInt a * toInt Kc :=
    evmMul_transport (a := a) (b := Kc) haw hKlt
      (by rw [hKc]; simp only [ipow255]; omega)
      (by rw [hKc]; simp only [ipow255]; omega)
  have e2' : toInt (evmMul a' Kc) = toInt a' * toInt Kc :=
    evmMul_transport (a := a') (b := Kc) haw' hKlt
      (by rw [hKc]; simp only [ipow255]; omega)
      (by rw [hKc]; simp only [ipow255]; omega)
  rw [hKc] at e2 e2'
  have e3 : toInt (evmAdd (evmMul a Kc) W) = toInt (evmMul a Kc) + toInt W :=
    evmAdd_transport (a := evmMul a Kc) (b := W) (evmMul_lt _ _) hWw
      (by rw [e2]; clear e2 e2' hKc hKlt; simp only [ipow255]; omega)
      (by rw [e2]; clear e2 e2' hKc hKlt; simp only [ipow255]; omega)
  have e3' : toInt (evmAdd (evmMul a' Kc) W) = toInt (evmMul a' Kc) + toInt W :=
    evmAdd_transport (a := evmMul a' Kc) (b := W) (evmMul_lt _ _) hWw
      (by rw [e2']; clear e2 e2' e3 hKc hKlt; simp only [ipow255]; omega)
      (by rw [e2']; clear e2 e2' e3 hKc hKlt; simp only [ipow255]; omega)
  have hBIlt : BIASc < 2 ^ 256 := by simp only [BIASc]; omega
  have hBI : toInt BIASc = (116873961749927929127912020551506849476088469858172 : Int) := by
    rw [toInt_of_lt (by simp only [BIASc]; omega)]
    simp only [BIASc]
    omega
  have e4 : toInt (evmAdd (evmAdd (evmMul a Kc) W) BIASc) =
      toInt (evmAdd (evmMul a Kc) W) + toInt BIASc :=
    evmAdd_transport (a := evmAdd (evmMul a Kc) W) (b := BIASc)
      (evmAdd_lt _ _) hBIlt
      (by rw [e3, e2, hBI]; clear e2 e2' e3 e3' hKc hKlt hBI hBIlt
          simp only [ipow255]; omega)
      (by rw [e3, e2, hBI]; clear e2 e2' e3 e3' hKc hKlt hBI hBIlt
          simp only [ipow255]; omega)
  have e4' : toInt (evmAdd (evmAdd (evmMul a' Kc) W) BIASc) =
      toInt (evmAdd (evmMul a' Kc) W) + toInt BIASc :=
    evmAdd_transport (a := evmAdd (evmMul a' Kc) W) (b := BIASc)
      (evmAdd_lt _ _) hBIlt
      (by rw [e3', e2', hBI]; clear e2 e2' e3 e3' e4 hKc hKlt hBI hBIlt
          simp only [ipow255]; omega)
      (by rw [e3', e2', hBI]; clear e2 e2' e3 e3' e4 hKc hKlt hBI hBIlt
          simp only [ipow255]; omega)
  have hord : toInt (evmAdd (evmAdd (evmMul a Kc) W) BIASc) ≤
      toInt (evmAdd (evmAdd (evmMul a' Kc) W) BIASc) := by
    have hmul : toInt a * (7450580596923828125 : Int) ≤
        toInt a' * (7450580596923828125 : Int) :=
      mul_le_mul_right_nonneg hA (by omega)
    rw [e4, e4', e3, e3', e2, e2']
    omega
  obtain ⟨w1lt, s1, s2⟩ :=
    evmSar_sandwich_72 (evmAdd_lt (evmAdd (evmMul a Kc) W) BIASc)
  obtain ⟨w1lt', s1', s2'⟩ :=
    evmSar_sandwich_72 (evmAdd_lt (evmAdd (evmMul a' Kc) W) BIASc)
  rw [evmAdd_zero w1lt, evmAdd_zero w1lt']
  generalize toInt (evmSar 72 (evmAdd (evmAdd (evmMul a Kc) W) BIASc)) =
    sA at s1 s2 ⊢
  generalize toInt (evmSar 72 (evmAdd (evmAdd (evmMul a' Kc) W) BIASc)) =
    sB at s1' s2' ⊢
  generalize toInt (evmAdd (evmAdd (evmMul a Kc) W) BIASc) = tA at s1 s2 hord
  generalize toInt (evmAdd (evmAdd (evmMul a' Kc) W) BIASc) = tB at s1' s2' hord
  omega

/-- Monotone tail: with the exponent word fixed and the `ln2 * k` term
bracketed, the mantissa-to-result map is nondecreasing. -/
theorem tail_mono {kw m m' : Nat} (h1 : MLO ≤ m) (h2 : m ≤ m') (h3 : m' < MHI)
    (hW1 : -(310963026251328585646059498617736427643747124513200 : Int) ≤
      toInt (evmMul LN2c kw))
    (hW2 : toInt (evmMul LN2c kw) ≤
      (523727202107500775824942313461450825505258314969600 : Int)) :
    toInt (lnTail 0 kw m) ≤ toInt (lnTail 0 kw m') := by
  have hm2 : m < MHI := by simp only [MLO, MHI] at *; omega
  have hm1' : MLO ≤ m' := by simp only [MLO, MHI] at *; omega
  have hA := r1_mono h1 h2 h3
  have hB := r1_bound h1 hm2
  have hB' := r1_bound hm1' h3
  have hr1w : x1W (zWord m) < 2 ^ 256 := by unfold x1W; exact evmSdiv_lt _ _
  have hr1w' : x1W (zWord m') < 2 ^ 256 := by unfold x1W; exact evmSdiv_lt _ _
  unfold lnTail
  exact affine_tail_mono hr1w hr1w' (evmMul_lt _ _) hA hB.1 hB.2 hB'.1 hB'.2 hW1 hW2

end LnGeneratedModel
