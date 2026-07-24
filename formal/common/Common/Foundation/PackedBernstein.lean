import Common.Foundation.Bernstein
import Common.Foundation.PackedShift
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Choose.Sum

namespace Common.Poly

open Finset

def binomialWeight (q : Nat → Int) (n i : Nat) : Int :=
  ∑ j ∈ Ico 0 (i + 1), q j * (Nat.choose (n - j) (i - j) : Int)

lemma binomial_row (n j : Nat) (x y : Int) (hj : j ≤ n) :
    (∑ i ∈ Ico j (n + 1),
        (Nat.choose (n - j) (i - j) : Int) * x ^ i * y ^ (n - i)) =
      x ^ j * (x + y) ^ (n - j) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : n + 1 - j = n - j + 1 := by omega
  rw [hlen]
  calc
    (∑ k ∈ range (n - j + 1),
        (Nat.choose (n - j) (j + k - j) : Int) * x ^ (j + k) *
          y ^ (n - (j + k))) =
      x ^ j * (∑ k ∈ range (n - j + 1),
        (Nat.choose (n - j) k : Int) * x ^ k * y ^ (n - j - k)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          simp only [Finset.mem_range] at hk
          have hkj : k ≤ n - j := by omega
          have hsub : n - (j + k) = n - j - k := by omega
          rw [Nat.add_sub_cancel_left, hsub, pow_add]
          ring
    _ = x ^ j * (x + y) ^ (n - j) := by
      rw [add_pow]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      ring

lemma binomial_transform_identity (q : Nat → Int) (n : Nat) (x y : Int) :
    (∑ i ∈ Ico 0 (n + 1),
        binomialWeight q n i * x ^ i * y ^ (n - i)) =
      ∑ j ∈ Ico 0 (n + 1), q j * x ^ j * (x + y) ^ (n - j) := by
  simp only [binomialWeight, Finset.sum_mul]
  rw [← Finset.sum_Ico_Ico_comm 0 (n + 1)
    (fun j i ↦ q j * (Nat.choose (n - j) (i - j) : Int) *
      x ^ i * y ^ (n - i))]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_Ico] at hj
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simpa [mul_assoc] using binomial_row n j x y (by omega)

lemma foldl_add_eq_sum (xs : List Nat) (f : Nat → Int) (z : Int) :
    xs.foldl (fun acc j ↦ acc + f j) z = z + (xs.map f).sum := by
  induction xs generalizing z with
  | nil => simp
  | cons j js ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      ring

lemma list_sum_map_range (f : Nat → Int) : ∀ n : Nat,
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append,
        Finset.sum_range_succ, ih]
      simp

lemma bernsteinWeight_eq_binomialWeight (q : List Int) (n i : Nat) :
    bernsteinWeight q n i = binomialWeight (fun j ↦ q.getD j 0) n i := by
  unfold bernsteinWeight binomialWeight
  rw [foldl_add_eq_sum]
  rw [zero_add, list_sum_map_range]
  simp

lemma homEvalI_eq_sum (q : List Int) (x y : Int) :
    homEvalI q x y =
      ∑ j ∈ Finset.range q.length,
        q.getD j 0 * x ^ j * y ^ (q.length - 1 - j) := by
  induction q with
  | nil => simp [homEvalI]
  | cons c cs ih =>
      rw [homEvalI]
      simp only [List.length_cons]
      rw [Finset.sum_range_succ']
      simp only [List.getD_cons_zero, pow_zero, mul_one,
        Nat.add_sub_cancel]
      rw [ih, Finset.mul_sum]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range] at hj
      rw [List.getD_cons_succ]
      have hsub : cs.length - (j + 1) = cs.length - 1 - j := by
        omega
      rw [hsub, pow_succ]
      ring

lemma bernstein_sum_eq_homEvalI (q : List Int) (n : Nat) (x y : Int)
    (hlen : q.length = n + 1) :
    (∑ i ∈ Ico 0 (n + 1),
        bernsteinWeight q n i * x ^ i * y ^ (n - i)) =
      homEvalI q x (x + y) := by
  simp_rw [bernsteinWeight_eq_binomialWeight]
  rw [binomial_transform_identity, homEvalI_eq_sum, hlen]
  simp

lemma scaleVariableAux_length (w : Int) (i : Nat) : ∀ C : List Int,
    (scaleVariableAux w i C).length = C.length := by
  intro C
  induction C generalizing i with
  | nil => rfl
  | cons c cs ih =>
      simp only [scaleVariableAux, List.length_cons]
      rw [ih]

lemma scaleVariable_length (w : Int) (C : List Int) :
    (scaleVariable w C).length = C.length := by
  exact scaleVariableAux_length w 0 C

lemma homEvalI_scaleVariableAux (w x : Int) (k : Nat) : ∀ C : List Int,
    homEvalI (scaleVariableAux w k C) x w =
      w ^ k * homEvalI C (x * w) w := by
  intro C
  induction C generalizing k with
  | nil => simp [scaleVariableAux, homEvalI]
  | cons c cs ih =>
      simp only [scaleVariableAux, homEvalI, scaleVariableAux_length]
      rw [ih, pow_succ]
      ring

lemma homEvalI_scaleVariable (w x : Int) (C : List Int) :
    homEvalI (scaleVariable w C) x w = homEvalI C (x * w) w := by
  simpa [scaleVariable] using homEvalI_scaleVariableAux w x 0 C

lemma homEvalI_scaleVariable_collapse (w x : Int) (C : List Int)
    (hC : C ≠ []) :
    homEvalI (scaleVariable w C) x w =
      w ^ (C.length - 1) * evalPoly C x := by
  rw [homEvalI_scaleVariable]
  match C with
  | [] => contradiction
  | c :: cs =>
      simpa using homEvalI_collapse x w c cs

def checkBernsteinWeightChunk (shifted weights : List Int)
    (width : Int) (n start count : Nat) : Bool :=
  let q := scaleVariable width shifted
  (Array.range count).all fun k ↦
    let i := start + k
    decide (weights.getD i 0 = bernsteinWeight q n i)

theorem checkBernsteinWeightChunk_sound
    (shifted weights : List Int) (width : Int) (n start count : Nat)
    (hcheck : checkBernsteinWeightChunk shifted weights width n start count = true) :
    ∀ i : Nat, start ≤ i → i < start + count →
      weights.getD i 0 =
        bernsteinWeight (scaleVariable width shifted) n i := by
  intro i hlo hhi
  unfold checkBernsteinWeightChunk at hcheck
  have hall : (Array.range count).all (fun k ↦
      decide (weights.getD (start + k) 0 =
        bernsteinWeight (scaleVariable width shifted) n (start + k))) := by
    simpa using hcheck
  rw [Array.all_iff_forall] at hall
  have h := hall (i - start) (by simp; omega) (by simp; omega)
  simpa [Nat.add_sub_of_le hlo] using h

lemma bernstein_emitted_shift_identity
    (C shifted : List Int) (a b t : Int)
    (hC : C ≠ []) (hlen : shifted.length = C.length)
    (heval : ∀ x : Int, evalPoly shifted x = evalPoly C (a + x)) :
    (∑ i ∈ Ico 0 (C.length - 1 + 1),
        bernsteinWeight (scaleVariable (b - a) shifted)
            (C.length - 1) i *
          (t - a) ^ i * (b - t) ^ (C.length - 1 - i)) =
      (b - a) ^ (C.length - 1) * evalPoly C t := by
  have hshifted : shifted ≠ [] := by
    intro hs
    have : C.length = 0 := by simpa [hs] using hlen.symm
    exact hC (List.eq_nil_of_length_eq_zero this)
  have hscaled :
      (scaleVariable (b - a) shifted).length = C.length - 1 + 1 := by
    rw [scaleVariable_length, hlen]
    have hpos : 0 < C.length := List.length_pos_iff.mpr hC
    omega
  rw [bernstein_sum_eq_homEvalI _ _ _ _ hscaled]
  have hxy : t - a + (b - t) = b - a := by ring
  rw [hxy]
  rw [homEvalI_scaleVariable_collapse _ _ _ hshifted, hlen, heval]
  rw [show a + (t - a) = t by ring]

theorem nonnegOn_of_emittedTaylor
    (C shifted weights : List Int) (a b : Int)
    (hC : C ≠ []) (hab : a < b)
    (hlen : shifted.length = C.length)
    (heval : ∀ x : Int, evalPoly shifted x = evalPoly C (a + x))
    (hweightsLen : weights.length = C.length)
    (hweights : ∀ i : Nat, i < C.length →
      weights.getD i 0 =
        bernsteinWeight (scaleVariable (b - a) shifted)
          (C.length - 1) i)
    (hnonneg : ∀ d ∈ weights, 0 ≤ d) : NonnegOn C a b := by
  intro t hat htb
  have hsum : 0 ≤
      ∑ i ∈ Ico 0 (C.length - 1 + 1),
        bernsteinWeight (scaleVariable (b - a) shifted)
            (C.length - 1) i *
          (t - a) ^ i * (b - t) ^ (C.length - 1 - i) := by
    apply Finset.sum_nonneg
    intro i hi
    simp only [Finset.mem_Ico] at hi
    have hiC : i < C.length := by
      have hpos : 0 < C.length := List.length_pos_iff.mpr hC
      omega
    rw [← hweights i hiC]
    have hiw : i < weights.length := by omega
    have hd := hnonneg (weights[i]) (List.getElem_mem hiw)
    rw [List.getD_eq_getElem weights 0 hiw]
    have hx : 0 ≤ t - a := by omega
    have hy : 0 ≤ b - t := by omega
    positivity
  rw [bernstein_emitted_shift_identity C shifted a b t hC hlen heval] at hsum
  have hw : 0 < (b - a) ^ (C.length - 1) := by
    have : 0 < b - a := by omega
    positivity
  nlinarith

theorem nonnegOn_of_packedBernstein
    {B : Nat} (C shifted weights : List Int) (a b : Int)
    {scalars : PackedShiftScalars}
    (hpacked : checkPackedShiftScalars B scalars = true)
    (hevidence : PackedShiftEvidence B C shifted a scalars)
    (hC : C ≠ []) (hab : a < b)
    (hlen : shifted.length = C.length)
    (hweightsLen : weights.length = C.length)
    (hweights : ∀ i : Nat, i < C.length →
      weights.getD i 0 =
        bernsteinWeight (scaleVariable (b - a) shifted)
          (C.length - 1) i)
    (hnonneg : ∀ d ∈ weights, 0 ≤ d) : NonnegOn C a b := by
  exact nonnegOn_of_emittedTaylor C shifted weights a b hC hab hlen
    (packedShift_eval hpacked hevidence) hweightsLen hweights hnonneg

end Common.Poly
