import LnProof.Mono.Top
import LnProof.Floor.Consts

open FormalYul
open FormalYul.Preservation

/-!
# Model-side decomposition for the floor specification

For a non-corrected input (`x ≠ 10^18`), the model's output word `r`
satisfies `r 2^72 ≤ V < (r+1) 2^72` where
`V = X1 Kc + ln2k(clz x) + BIASc` is the exact pre-shift accumulator.
This is the bridge from the EVM word pipeline to the exponential-cap
arithmetic: dividing by `2^72 · 10^27` turns `V` into the sum of exponent
arguments handled by the caps of `LnProof.Floor.Consts`.
-/

set_option maxRecDepth 4096

namespace LnFloor

open LnYul Common.Poly

/-- Mantissa word of `x`. -/
def mant (x : Nat) : Nat := evmShr 160 (evmShl (evmClz x) x)

/-- Binade window for the mantissa, low-shift side. -/
theorem mant_window_le {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hc : evmClz x ≤ 160) :
    mant x * 2 ^ (160 - evmClz x) ≤ x ∧
      x < (mant x + 1) * 2 ^ (160 - evmClz x) := by
  obtain ⟨me, _, _⟩ := mant_facts h1 h2
  have hclz : evmClz x = 255 - Nat.log2 x := evmClz_eq h1 (by omega)
  have hm : mant x = x * 2 ^ (255 - Nat.log2 x) / 2 ^ 160 := me
  rw [hclz] at hc ⊢
  have hdm := Nat.div_add_mod (x * 2 ^ (255 - Nat.log2 x)) (2 ^ 160)
  have hml := Nat.mod_lt (x * 2 ^ (255 - Nat.log2 x)) (y := 2 ^ 160) (by decide)
  have hsplit : 2 ^ (255 - Nat.log2 x) * 2 ^ (160 - (255 - Nat.log2 x)) = 2 ^ 160 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hm]
  generalize hgq : x * 2 ^ (255 - Nat.log2 x) / 2 ^ 160 = q at *
  generalize hgA : (2 : Nat) ^ (255 - Nat.log2 x) = A at *
  generalize hgB : (2 : Nat) ^ (160 - (255 - Nat.log2 x)) = B at *
  have hA0 : 0 < A := by rw [← hgA]; exact Nat.pow_pos (by omega)
  constructor
  · refine Nat.le_of_mul_le_mul_left ?_ hA0
    have e1 : A * (q * B) = 2 ^ 160 * q := by
      rw [show A * (q * B) = q * (A * B) from by
        simp only [Nat.mul_left_comm], hsplit]
      exact Nat.mul_comm _ _
    have e2 : A * x = x * A := Nat.mul_comm _ _
    generalize hg1 : A * (q * B) = T1 at e1 ⊢
    generalize hg3 : A * x = T3 at e2 ⊢
    generalize hg4 : x * A = T4 at e2 hdm
    generalize hg5 : 2 ^ 160 * q = T5 at e1 hdm
    omega
  · have hlt : x * A < (q + 1) * 2 ^ 160 := by
      have e : (q + 1) * 2 ^ 160 = 2 ^ 160 * q + 2 ^ 160 := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
      omega
    refine Nat.lt_of_mul_lt_mul_left (a := A) ?_
    have e1 : A * x = x * A := Nat.mul_comm _ _
    have e2 : A * ((q + 1) * B) = (q + 1) * 2 ^ 160 := by
      rw [show A * ((q + 1) * B) = (q + 1) * (A * B) from by
        simp only [Nat.mul_assoc, Nat.mul_comm], hsplit]
    generalize hg1 : A * x = T1 at e1 ⊢
    generalize hg2 : x * A = T2 at e1 hlt
    generalize hg3 : A * ((q + 1) * B) = T3 at e2 ⊢
    generalize hg5 : (q + 1) * 2 ^ 160 = T5 at e2 hlt
    omega

/-- Binade window, high-shift side: the mantissa is exact. -/
theorem mant_window_gt {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hc : 160 < evmClz x) :
    mant x = x * 2 ^ (evmClz x - 160) := by
  obtain ⟨me, _, _⟩ := mant_facts h1 h2
  have hclz : evmClz x = 255 - Nat.log2 x := evmClz_eq h1 (by omega)
  have hm : mant x = x * 2 ^ (255 - Nat.log2 x) / 2 ^ 160 := me
  rw [hclz] at hc ⊢
  have hsplit : (2 : Nat) ^ (255 - Nat.log2 x) =
      2 ^ 160 * 2 ^ ((255 - Nat.log2 x) - 160) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hm, hsplit]
  have e : x * (2 ^ 160 * 2 ^ ((255 - Nat.log2 x) - 160)) =
      x * 2 ^ ((255 - Nat.log2 x) - 160) * 2 ^ 160 := by
    simp only [Nat.mul_comm, Nat.mul_left_comm]
  rw [e]
  exact Nat.mul_div_cancel _ (by decide)

theorem clz_bounds {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) :
    1 ≤ evmClz x ∧ evmClz x ≤ 255 := by
  have hclz : evmClz x = 255 - Nat.log2 x := evmClz_eq h1 (by omega)
  have hlog : Nat.log2 x < 255 := (Nat.log2_lt (by omega)).mpr (by omega)
  omega

/-- Signed `ln2 * k` summand for clz value `c`. -/
def ln2kInt (c : Nat) : Int :=
  if c ≤ 160 then (LN2c : Int) * ((160 - c : Nat) : Int)
  else -((LN2c : Int) * ((c - 160 : Nat) : Int))

theorem ln2kInt_eq {c : Nat} (hc : c < 256) :
    int256 (evmMul LN2c (evmSub 160 c)) = ln2kInt c :=
  ln2k_exact hc

/-- The pre-shift accumulator decomposes exactly. -/
theorem r4_value {m : Nat} (h1 : MLO ≤ m) (h2 : m < MHI) {c : Nat} (hc : c < 256) :
    int256 (evmAdd (evmAdd (evmMul (x1W (zWord m)) Kc) (evmMul LN2c (evmSub 160 c)))
        BIASc) =
      int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551560854268589826112230 := by
  have hB := r1_bound h1 h2
  have hr1w : x1W (zWord m) < 2 ^ 256 := by unfold x1W; exact evmSdiv_lt _ _
  have hW := ln2k_bound hc
  generalize hg : x1W (zWord m) = r1w at *
  have hKlt : Kc < 2 ^ 256 := by simp only [Kc]; omega
  have hKc : int256 Kc = (7450580596923828125 : Int) := by
    rw [toInt_of_lt (by simp only [Kc]; omega)]
    simp only [Kc]
    omega
  have e2 : int256 (evmMul r1w Kc) = int256 r1w * int256 Kc :=
    evmMul_transport (a := r1w) (b := Kc) hr1w hKlt
      (by rw [hKc]; simp only [ipow255]; omega)
      (by rw [hKc]; simp only [ipow255]; omega)
  rw [hKc] at e2
  have e3 : int256 (evmAdd (evmMul r1w Kc) (evmMul LN2c (evmSub 160 c))) =
      int256 (evmMul r1w Kc) + int256 (evmMul LN2c (evmSub 160 c)) :=
    evmAdd_transport (a := evmMul r1w Kc) (b := evmMul LN2c (evmSub 160 c))
      (evmMul_lt _ _) (evmMul_lt _ _)
      (by rw [e2]; clear e2 hKc hKlt; simp only [ipow255]; omega)
      (by rw [e2]; clear e2 hKc hKlt; simp only [ipow255]; omega)
  have hBIlt : BIASc < 2 ^ 256 := by simp only [BIASc]; omega
  have hBI : int256 BIASc = (116873961749927929127912020551560854268589826112230 : Int) := by
    rw [toInt_of_lt (by simp only [BIASc]; omega)]
    simp only [BIASc]
    omega
  have e4 : int256 (evmAdd (evmAdd (evmMul r1w Kc) (evmMul LN2c (evmSub 160 c))) BIASc) =
      int256 (evmAdd (evmMul r1w Kc) (evmMul LN2c (evmSub 160 c))) + int256 BIASc :=
    evmAdd_transport (a := evmAdd (evmMul r1w Kc) (evmMul LN2c (evmSub 160 c)))
      (b := BIASc) (evmAdd_lt _ _) hBIlt
      (by rw [e3, e2, hBI]; clear e2 e3 hKc hKlt hBI hBIlt; simp only [ipow255]; omega)
      (by rw [e3, e2, hBI]; clear e2 e3 hKc hKlt hBI hBIlt; simp only [ipow255]; omega)
  rw [e4, e3, e2, hBI, ← ln2kInt_eq hc]

/-- The corrected body is nonzero away from `10^18`: monotonicity pins it
strictly negative below `10^18` (it is `≤ lnWad(10^18 - 1) < 0`) and strictly
positive above (it is `≥ lnWad(10^18 + 1) > 0`). The two neighbour values are
decided directly. -/
theorem lnWadToRayBody_ne_zero {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hne : x ≠ 1000000000000000000) : int256 (lnWadToRayBody x) ≠ 0 := by
  rcases Nat.lt_trichotomy x 1000000000000000000 with hlt | heq | hgt
  · have hmono := toInt_of_sle (lnWadToRayBody_lt (by omega)) (lnWadToRayBody_lt (by omega))
      (lnWadToRayBody_mono h1 (by omega : x ≤ 999999999999999999) (by decide))
    have hlo : int256 (lnWadToRayBody 999999999999999999) < 0 := by
      rw [lnWadToRayBody_eq_tail (by norm_num : 999999999999999999 < 2 ^ 256),
        bodyMantissa_wad_minus, bodyClz_wad_minus]
      decide
    omega
  · exact absurd heq hne
  · have hmono := toInt_of_sle (lnWadToRayBody_lt (by omega)) (lnWadToRayBody_lt (by omega))
      (lnWadToRayBody_mono (by omega : 0 < 1000000000000000001)
        (by omega : 1000000000000000001 ≤ x) h2)
    have hhi : 0 < int256 (lnWadToRayBody 1000000000000000001) := by
      rw [lnWadToRayBody_eq_tail (by norm_num : 1000000000000000001 < 2 ^ 256),
        bodyMantissa_wad_plus, bodyClz_wad_plus]
      decide
    omega

/-- For non-corrected inputs the body word floors the accumulator:
`r 2^72 ≤ V < (r + 1) 2^72`. -/
theorem lnWadToRayBody_floor_bracket {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255)
    (hne : x ≠ 1000000000000000000) :
    int256 (lnWadToRayBody x) * 4722366482869645213696 ≤
        int256 (x1W (zWord (mant x))) * 7450580596923828125 + ln2kInt (evmClz x) +
          116873961749927929127912020551560854268589826112230 ∧
      int256 (x1W (zWord (mant x))) * 7450580596923828125 + ln2kInt (evmClz x) +
          116873961749927929127912020551560854268589826112230 <
        int256 (lnWadToRayBody x) * 4722366482869645213696 +
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
  -- The body is the self-corrected floor `s + (s == -1)`; off `10^18` it is `s`.
  have hmc : lnWadToRayBody x =
      evmAdd (evmIszero (evmNot (evmSar 72 (evmAdd (evmAdd (evmMul (x1W (zWord (mant x))) Kc)
        (evmMul LN2c (evmSub 160 (evmClz x)))) BIASc))))
      (evmSar 72 (evmAdd (evmAdd (evmMul (x1W (zWord (mant x))) Kc)
        (evmMul LN2c (evmSub 160 (evmClz x)))) BIASc)) := by
    rw [lnWadToRayBody_eq_tail hx256]; rfl
  have hsne : evmSar 72 (evmAdd (evmAdd (evmMul (x1W (zWord (mant x))) Kc)
      (evmMul LN2c (evmSub 160 (evmClz x)))) BIASc) ≠ 2 ^ 256 - 1 := by
    intro hs
    apply lnWadToRayBody_ne_zero h1 h2 hne
    rw [hmc, hs]; decide
  have hbody : lnWadToRayBody x =
      evmSar 72 (evmAdd (evmAdd (evmMul (x1W (zWord (mant x))) Kc)
        (evmMul LN2c (evmSub 160 (evmClz x)))) BIASc) := by
    rw [hmc, corr_eq hsarlt, if_neg hsne]
  obtain ⟨wlt, s1, s2⟩ := evmSar_sandwich_72 (evmAdd_lt
    (evmAdd (evmMul (x1W (zWord (mant x))) Kc)
      (evmMul LN2c (evmSub 160 (evmClz x)))) BIASc)
  rw [hbody]
  rw [hr4] at s1 s2
  exact ⟨s1, s2⟩

end LnFloor
