import LnProof.TopMono
import LnProof.FloorConsts

/-!
# Model-side decomposition for the floor specification

For a non-corrected input (`x ≠ 10^18`), the model's output word `r`
satisfies `r 2^72 ≤ V < (r+1) 2^72` where
`V = X1 Kc + ln2k(clz x) + BIASc` is the exact pre-shift accumulator.
This is the bridge from the EVM word pipeline to the exponential-cap
arithmetic: dividing by `2^72 · 10^27` turns `V` into the sum of exponent
arguments handled by the caps of `LnProof.FloorConsts`.
-/

set_option maxRecDepth 4096

namespace LnFloor

open LnGeneratedModel LnPoly

/-- Mantissa word of `x`. -/
def mant (x : Nat) : Nat := evmShr 160 (evmShl (evmClz x) x)

/-- Signed `ln2 * k` summand for clz value `c`. -/
def ln2kInt (c : Nat) : Int :=
  if c ≤ 160 then (LN2c : Int) * ((160 - c : Nat) : Int)
  else -((LN2c : Int) * ((c - 160 : Nat) : Int))

theorem ln2kInt_eq {c : Nat} (hc : c < 256) :
    toInt (evmMul LN2c (evmSub 160 c)) = ln2kInt c :=
  ln2k_exact hc

theorem ln2kInt_bound {c : Nat} (hc : c < 256) :
    -(310963026251328585646059498617736427643747124513200 : Int) ≤ ln2kInt c ∧
      ln2kInt c ≤ (523727202107500775824942313461450825505258314969600 : Int) := by
  rw [← ln2kInt_eq hc]
  exact ln2k_bound hc

/-- The pre-shift accumulator decomposes exactly. -/
theorem r4_value {m : Nat} (h1 : MLO ≤ m) (h2 : m < MHI) {c : Nat} (hc : c < 256) :
    toInt (evmAdd (evmAdd (evmMul (x1W (zWord m)) Kc) (evmMul LN2c (evmSub 160 c)))
        BIASc) =
      toInt (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551516284764321243411868 := by
  have hB := r1_bound h1 h2
  have hr1w : x1W (zWord m) < 2 ^ 256 := by unfold x1W; exact evmSdiv_lt _ _
  have hW := ln2k_bound hc
  generalize hg : x1W (zWord m) = r1w at *
  have hKlt : Kc < 2 ^ 256 := by simp only [Kc]; omega
  have hKc : toInt Kc = (7450580596923828125 : Int) := by
    rw [toInt_of_lt (by simp only [Kc]; omega)]
    simp only [Kc]
    omega
  have e2 : toInt (evmMul r1w Kc) = toInt r1w * toInt Kc :=
    evmMul_transport (a := r1w) (b := Kc) hr1w hKlt
      (by rw [hKc]; simp only [ipow255]; omega)
      (by rw [hKc]; simp only [ipow255]; omega)
  rw [hKc] at e2
  have e3 : toInt (evmAdd (evmMul r1w Kc) (evmMul LN2c (evmSub 160 c))) =
      toInt (evmMul r1w Kc) + toInt (evmMul LN2c (evmSub 160 c)) :=
    evmAdd_transport (a := evmMul r1w Kc) (b := evmMul LN2c (evmSub 160 c))
      (evmMul_lt _ _) (evmMul_lt _ _)
      (by rw [e2]; clear e2 hKc hKlt; simp only [ipow255]; omega)
      (by rw [e2]; clear e2 hKc hKlt; simp only [ipow255]; omega)
  have hBIlt : BIASc < 2 ^ 256 := by simp only [BIASc]; omega
  have hBI : toInt BIASc = (116873961749927929127912020551516284764321243411868 : Int) := by
    rw [toInt_of_lt (by simp only [BIASc]; omega)]
    simp only [BIASc]
    omega
  have e4 : toInt (evmAdd (evmAdd (evmMul r1w Kc) (evmMul LN2c (evmSub 160 c))) BIASc) =
      toInt (evmAdd (evmMul r1w Kc) (evmMul LN2c (evmSub 160 c))) + toInt BIASc :=
    evmAdd_transport (a := evmAdd (evmMul r1w Kc) (evmMul LN2c (evmSub 160 c)))
      (b := BIASc) (evmAdd_lt _ _) hBIlt
      (by rw [e3, e2, hBI]; clear e2 e3 hKc hKlt hBI hBIlt; simp only [ipow255]; omega)
      (by rw [e3, e2, hBI]; clear e2 e3 hKc hKlt hBI hBIlt; simp only [ipow255]; omega)
  rw [e4, e3, e2, hBI, ← ln2kInt_eq hc]

/-- The corrected model is nonzero away from `10^18`: monotonicity pins it
strictly negative below `10^18` (it is `≤ lnWad(10^18 - 1) < 0`) and strictly
positive above (it is `≥ lnWad(10^18 + 1) > 0`). The two neighbour values are
decided directly. -/
theorem model_ne_zero {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hne : x ≠ 1000000000000000000) : toInt (model_ln_wad_evm x) ≠ 0 := by
  rcases Nat.lt_trichotomy x 1000000000000000000 with hlt | heq | hgt
  · have hmono := toInt_of_sle (model_lt (by omega)) (model_lt (by omega))
      (model_ln_wad_mono h1 (by omega : x ≤ 999999999999999999) (by decide))
    have hlo : toInt (model_ln_wad_evm 999999999999999999) < 0 := by decide +kernel
    omega
  · exact absurd heq hne
  · have hmono := toInt_of_sle (model_lt (by omega)) (model_lt (by omega))
      (model_ln_wad_mono (by omega : 0 < 1000000000000000001)
        (by omega : 1000000000000000001 ≤ x) h2)
    have hhi : 0 < toInt (model_ln_wad_evm 1000000000000000001) := by decide +kernel
    omega

/-- For non-corrected inputs the model word floors the accumulator:
`r 2^72 ≤ V < (r + 1) 2^72`. -/
theorem model_floor_bracket {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hne : x ≠ 1000000000000000000) :
    toInt (model_ln_wad_evm x) * 4722366482869645213696 ≤
        toInt (x1W (zWord (mant x))) * 7450580596923828125 + ln2kInt (evmClz x) +
          116873961749927929127912020551516284764321243411868 ∧
      toInt (x1W (zWord (mant x))) * 7450580596923828125 + ln2kInt (evmClz x) +
          116873961749927929127912020551516284764321243411868 <
        toInt (model_ln_wad_evm x) * 4722366482869645213696 +
          4722366482869645213696 := by
  have hx256 : x < 2 ^ 256 := by omega
  have hc : evmClz x < 256 := by
    rw [evmClz_eq h1 hx256]
    omega
  obtain ⟨me, mlo, mhi⟩ := mant_facts h1 h2
  have hmant : MLO ≤ mant x ∧ mant x < MHI := by
    unfold mant
    rw [me]
    exact ⟨mlo, mhi⟩
  have hr4 := r4_value hmant.1 hmant.2 hc
  have hsarlt : evmSar 72 (evmAdd (evmAdd (evmMul (x1W (zWord (mant x))) Kc)
      (evmMul LN2c (evmSub 160 (evmClz x)))) BIASc) < 2 ^ 256 :=
    (evmSar_sandwich_72 (evmAdd_lt _ _)).1
  -- The model is the self-corrected floor `s + (s == -1)`; off `10^18` it is `s`.
  have hmc : model_ln_wad_evm x =
      evmAdd (evmIszero (evmNot (evmSar 72 (evmAdd (evmAdd (evmMul (x1W (zWord (mant x))) Kc)
        (evmMul LN2c (evmSub 160 (evmClz x)))) BIASc))))
      (evmSar 72 (evmAdd (evmAdd (evmMul (x1W (zWord (mant x))) Kc)
        (evmMul LN2c (evmSub 160 (evmClz x)))) BIASc)) := by
    rw [model_eq_tail hx256]; rfl
  have hsne : evmSar 72 (evmAdd (evmAdd (evmMul (x1W (zWord (mant x))) Kc)
      (evmMul LN2c (evmSub 160 (evmClz x)))) BIASc) ≠ 2 ^ 256 - 1 := by
    intro hs
    apply model_ne_zero h1 h2 hne
    rw [hmc, hs]; decide
  have hmodel : model_ln_wad_evm x =
      evmSar 72 (evmAdd (evmAdd (evmMul (x1W (zWord (mant x))) Kc)
        (evmMul LN2c (evmSub 160 (evmClz x)))) BIASc) := by
    rw [hmc, corr_eq hsarlt, if_neg hsne]
  obtain ⟨wlt, s1, s2⟩ := evmSar_sandwich_72 (evmAdd_lt
    (evmAdd (evmMul (x1W (zWord (mant x))) Kc)
      (evmMul LN2c (evmSub 160 (evmClz x)))) BIASc)
  rw [hmodel]
  rw [hr4] at s1 s2
  exact ⟨s1, s2⟩

end LnFloor
