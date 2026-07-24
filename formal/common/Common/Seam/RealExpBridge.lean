import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Common.Foundation.ExpSum

open scoped BigOperators

/-!
# Real-exponential bridge for the partial-sum caps

`capUB`/`capLB` are integer-scaled bounds on the truncated Taylor sums of
`e^(p/q)`. This module connects them to `Real.exp`: the partial sums of
`exp` agree with `expNum`, so an upper cap bounds `Real.exp` from above and a
lower cap bounds it from below. These bridges are function-agnostic — they
only use the `Common.Exp` partial-sum interface and Mathlib's `Real.exp`.
-/

namespace Common.RealExpBridge

open Common.Exp

noncomputable section

lemma fact_eq_factorial (n : Nat) : fact n = Nat.factorial n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [fact, Nat.factorial_succ, ih]

lemma tsum_nat_cast_sum_range (n : Nat) (f : Nat → Nat) :
    ((Common.Exp.tsum n f : Nat) : Real) = ∑ j ∈ Finset.range (n + 1), (f j : Real) := by
  induction n with
  | zero => simp [Common.Exp.tsum]
  | succ k ih =>
      simp [Common.Exp.tsum, ih, Finset.sum_range_succ, Nat.cast_add]

lemma expNum_div_eq_sum_range (n p q : Nat) (hq : 0 < q) :
    (expNum n p q : Real) / ((fact n * q ^ n : Nat) : Real) =
      ∑ j ∈ Finset.range (n + 1), ((p : Real) / q) ^ j / ((fact j : Nat) : Real) := by
  rw [expNum_eq_tsum]
  rw [show ((Common.Exp.tsum n (fun j => ffacAux j (n - j) * p ^ j * q ^ (n - j)) : Nat) : Real) =
      ∑ j ∈ Finset.range (n + 1), ((ffacAux j (n - j) * p ^ j * q ^ (n - j) : Nat) : Real) from
      tsum_nat_cast_sum_range n (fun j => ffacAux j (n - j) * p ^ j * q ^ (n - j))]
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ n := Nat.lt_succ.mp (Finset.mem_range.mp hj)
  have hqn : (q : Real) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have hfactj : ((fact j : Nat) : Real) ≠ 0 := by
    exact_mod_cast ne_of_gt (fact_pos j)
  have hfactn : ((fact n : Nat) : Real) ≠ 0 := by
    exact_mod_cast ne_of_gt (fact_pos n)
  have hden : (((fact n * q ^ n : Nat) : Real)) ≠ 0 := by
    exact_mod_cast ne_of_gt (Nat.mul_pos (fact_pos n) (Nat.pow_pos hq))
  have hff : (ffacAux j (n - j) * fact j : Nat) = fact n := by
    rw [ffacAux_mul_fact]
    congr 1
    omega
  have hffR : ((ffacAux j (n - j) : Nat) : Real) * ((fact j : Nat) : Real) = ((fact n : Nat) : Real) := by
    norm_num [← Nat.cast_mul, hff]
  have hpow : (q : Real) ^ n = (q : Real) ^ j * (q : Real) ^ (n - j) := by
    rw [← pow_add]
    congr 1
    omega
  norm_num [Nat.cast_mul, Nat.cast_pow]
  field_simp [hden, hfactj, hfactn, hqn]
  rw [hpow]
  ring_nf
  rw [← hffR]
  ring

lemma exp_hasSum (t : Real) : HasSum (fun n : Nat => t ^ n / ((fact n : Nat) : Real)) (Real.exp t) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝕂 := Real) (𝔸 := Real) t
  simpa [fact_eq_factorial, Real.exp_eq_exp_ℝ] using h

lemma expTerm_nonneg {p q : Nat} (hq : 0 < q) (i : Nat) :
    0 ≤ ((p : Real) / q) ^ i / ((fact i : Nat) : Real) := by
  have hpq : 0 ≤ (p : Real) / q := by positivity
  have hf : 0 ≤ ((fact i : Nat) : Real) := by positivity
  exact div_nonneg (pow_nonneg hpq i) hf

lemma div_le_of_cross_mul_le {a b c d : Real} (hc : 0 < c) (hd : 0 < d)
    (h : a * d ≤ b * c) : a / c ≤ b / d := by
  by_contra hnot
  have hlt : b / d < a / c := lt_of_not_ge hnot
  have hlt1 := mul_lt_mul_of_pos_right hlt hc
  have hlt2 := mul_lt_mul_of_pos_right hlt1 hd
  field_simp [hc.ne', hd.ne'] at hlt2
  nlinarith

lemma capUB_bound_real {p q y w : Nat} (hq : 0 < q) (hw : 0 < w)
    (n : Nat) (h : capUB p q y w) :
    (expNum n p q : Real) / ((fact n * q ^ n : Nat) : Real) ≤ (y : Real) / w := by
  have hnat := h n
  have hreal : (expNum n p q : Real) * (w : Real) ≤
      (y : Real) * ((fact n * q ^ n : Nat) : Real) := by
    exact_mod_cast hnat
  have hdenpos : 0 < ((fact n * q ^ n : Nat) : Real) := by
    exact_mod_cast Nat.mul_pos (fact_pos n) (Nat.pow_pos hq)
  have hwpos : 0 < (w : Real) := by exact_mod_cast hw
  exact div_le_of_cross_mul_le hdenpos hwpos hreal

lemma capLB_bound_real {p q y w : Nat} (hq : 0 < q) (hw : 0 < w)
    {n : Nat} (h : y * (fact n * q ^ n) ≤ expNum n p q * w) :
    (y : Real) / w ≤ (expNum n p q : Real) / ((fact n * q ^ n : Nat) : Real) := by
  have hreal : (y : Real) * ((fact n * q ^ n : Nat) : Real) ≤
      (expNum n p q : Real) * (w : Real) := by
    exact_mod_cast h
  have hdenpos : 0 < ((fact n * q ^ n : Nat) : Real) := by
    exact_mod_cast Nat.mul_pos (fact_pos n) (Nat.pow_pos hq)
  have hwpos : 0 < (w : Real) := by exact_mod_cast hw
  exact div_le_of_cross_mul_le hwpos hdenpos hreal

lemma exp_le_of_capUB {p q y w : Nat} (hq : 0 < q) (hw : 0 < w)
    (h : capUB p q y w) : Real.exp ((p : Real) / q) ≤ (y : Real) / w := by
  have hs := exp_hasSum ((p : Real) / q)
  rw [← hs.tsum_eq]
  refine Summable.tsum_le_of_sum_le hs.summable ?_
  intro s
  by_cases hsempty : s.Nonempty
  · let N := s.max' hsempty
    have hsub : s ⊆ Finset.range (N + 1) := by
      intro i hi
      exact Finset.mem_range.mpr (Nat.lt_succ.mpr (Finset.le_max' s i hi))
    calc ∑ i ∈ s, ((p : Real) / q) ^ i / ((fact i : Nat) : Real)
        ≤ ∑ i ∈ Finset.range (N + 1), ((p : Real) / q) ^ i / ((fact i : Nat) : Real) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi his => expTerm_nonneg hq i)
      _ = (expNum N p q : Real) / ((fact N * q ^ N : Nat) : Real) := by
          rw [expNum_div_eq_sum_range N p q hq]
      _ ≤ (y : Real) / w := capUB_bound_real hq hw N h
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsempty
    rw [hs0]
    simp only [Finset.sum_empty]
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)

lemma le_exp_of_capLB {p q y w : Nat} (hq : 0 < q) (hw : 0 < w)
    (h : capLB p q y w) : (y : Real) / w ≤ Real.exp ((p : Real) / q) := by
  obtain ⟨n, hn⟩ := h
  have hs := exp_hasSum ((p : Real) / q)
  rw [← hs.tsum_eq]
  calc (y : Real) / w
      ≤ (expNum n p q : Real) / ((fact n * q ^ n : Nat) : Real) := capLB_bound_real hq hw hn
    _ = ∑ i ∈ Finset.range (n + 1), ((p : Real) / q) ^ i / ((fact i : Nat) : Real) := by
        rw [expNum_div_eq_sum_range n p q hq]
    _ ≤ ∑' i : Nat, ((p : Real) / q) ^ i / ((fact i : Nat) : Real) := by
        exact Summable.sum_le_tsum _ (fun i hi => expTerm_nonneg hq i) hs.summable

lemma partial_sum_le_exp {p q : Nat} (hq : 0 < q) (n : Nat) :
    (expNum n p q : Real) / ((fact n * q ^ n : Nat) : Real) ≤
      Real.exp ((p : Real) / q) := by
  have hs := exp_hasSum ((p : Real) / q)
  rw [expNum_div_eq_sum_range n p q hq, ← hs.tsum_eq]
  exact Summable.sum_le_tsum (Finset.range (n + 1))
    (fun i _ => expTerm_nonneg hq i) hs.summable

lemma capUB_of_exp_le {p q y w : Nat} (hq : 0 < q) (hw : 0 < w)
    (h : Real.exp ((p : Real) / q) ≤ (y : Real) / w) : capUB p q y w := by
  intro n
  have hratio :
      (expNum n p q : Real) / ((fact n * q ^ n : Nat) : Real) ≤ (y : Real) / w :=
    (partial_sum_le_exp hq n).trans h
  have hdenpos : 0 < ((fact n * q ^ n : Nat) : Real) := by
    exact_mod_cast Nat.mul_pos (fact_pos n) (Nat.pow_pos hq)
  have hwpos : 0 < (w : Real) := by exact_mod_cast hw
  have hcross :
      (expNum n p q : Real) * (w : Real) ≤
        (y : Real) * ((fact n * q ^ n : Nat) : Real) :=
    (div_le_div_iff₀ hdenpos hwpos).mp hratio
  exact_mod_cast hcross

lemma capLB_of_lt_exp {p q y w : Nat} (hq : 0 < q) (hw : 0 < w)
    (h : (y : Real) / w < Real.exp ((p : Real) / q)) : capLB p q y w := by
  have hs := exp_hasSum ((p : Real) / q)
  have heventually : ∀ᶠ n : Nat in Filter.atTop,
      (y : Real) / w < ∑ i ∈ Finset.range n,
        ((p : Real) / q) ^ i / ((fact i : Nat) : Real) :=
    (tendsto_order.mp hs.tendsto_sum_nat).1 _ h
  obtain ⟨n, hn⟩ := heventually.exists
  have hterm : 0 ≤ ((p : Real) / q) ^ n / ((fact n : Nat) : Real) :=
    expTerm_nonneg hq n
  have hratio : (y : Real) / w ≤
      (expNum n p q : Real) / ((fact n * q ^ n : Nat) : Real) := by
    rw [expNum_div_eq_sum_range n p q hq, Finset.sum_range_succ]
    linarith
  have hwpos : 0 < (w : Real) := by exact_mod_cast hw
  have hdenpos : 0 < ((fact n * q ^ n : Nat) : Real) := by
    exact_mod_cast Nat.mul_pos (fact_pos n) (Nat.pow_pos hq)
  have hcross : (y : Real) * ((fact n * q ^ n : Nat) : Real) ≤
      (expNum n p q : Real) * (w : Real) :=
    (div_le_div_iff₀ hwpos hdenpos).mp hratio
  refine ⟨n, ?_⟩
  exact_mod_cast hcross

end

end Common.RealExpBridge
