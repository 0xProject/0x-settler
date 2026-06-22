import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import LnProof.ExpSum
import LnProof.LnRealSpec

open scoped BigOperators

namespace LnRealBridge

open LnExp

noncomputable section

lemma fact_eq_factorial (n : Nat) : fact n = Nat.factorial n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [fact, Nat.factorial_succ, ih]

lemma tsum_nat_cast_sum_range (n : Nat) (f : Nat → Nat) :
    ((LnExp.tsum n f : Nat) : Real) = ∑ j ∈ Finset.range (n + 1), (f j : Real) := by
  induction n with
  | zero => simp [LnExp.tsum]
  | succ k ih =>
      simp [LnExp.tsum, ih, Finset.sum_range_succ, Nat.cast_add]

lemma expNum_div_eq_sum_range (n p q : Nat) (hq : 0 < q) :
    (expNum n p q : Real) / ((fact n * q ^ n : Nat) : Real) =
      ∑ j ∈ Finset.range (n + 1), ((p : Real) / q) ^ j / ((fact j : Nat) : Real) := by
  rw [expNum_eq_tsum]
  rw [show ((LnExp.tsum n (fun j => ffacAux j (n - j) * p ^ j * q ^ (n - j)) : Nat) : Real) =
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

def QS : Nat := 10 ^ 27 * 2 ^ 99

def CutExpLe (p q y w : Nat) : Prop := capUB p q y w
def CutRatioLeExp (y w p q : Nat) : Prop := capLB p q y w

def CutLeLogWadRay (r : Int) (x : Nat) : Prop :=
  if 0 <= r then
    CutExpLe (r.toNat * 2 ^ 99) QS x (10 ^ 18)
  else
    CutRatioLeExp (10 ^ 18) x ((-r).toNat * 2 ^ 99) QS

def CutLogWadRayLtWithMargin (x : Nat) (b : Int) : Prop :=
  if 1 <= b then
    CutRatioLeExp (x * 10 ^ 31) (10 ^ 18 * (10 ^ 31 - 10)) (b.toNat * 2 ^ 99) QS
  else
    CutExpLe ((-b).toNat * 2 ^ 99) QS (10 ^ 18 * (10 ^ 31 - 10)) (x * 10 ^ 31)

def CutLnWadRayBracket (r : Int) (x : Nat) : Prop :=
  CutLeLogWadRay r x ∧ CutLogWadRayLtWithMargin x (r + 2)

def CutLnWadSpec (ray wad : Int) (x : Nat) : Prop :=
  CutLnWadRayBracket ray x ∧ wad * 1000000000 <= ray ∧ ray < (wad + 1) * 1000000000

lemma QS_pos : 0 < QS := by decide

lemma ray_exp_arg_of_nonneg {r : Int} (hr : 0 ≤ r) :
    (((r.toNat * 2 ^ 99 : Nat) : Real) / ((QS : Nat) : Real)) =
      (r : Real) / ((10 ^ 27 : Nat) : Real) := by
  have hrnat : ((r.toNat : Nat) : Real) = (r : Real) := by
    exact_mod_cast Int.toNat_of_nonneg hr
  unfold QS
  norm_num [Nat.cast_mul, Nat.cast_pow, hrnat]
  field_simp
  ring

lemma ray_exp_arg_of_neg {r : Int} (hr : r < 0) :
    ((((-r).toNat * 2 ^ 99 : Nat) : Real) / ((QS : Nat) : Real)) =
      -((r : Real) / ((10 ^ 27 : Nat) : Real)) := by
  rw [ray_exp_arg_of_nonneg (r := -r) (by omega)]
  norm_num [Int.cast_neg]
  ring

lemma ray_exp_arg_of_nonpos {r : Int} (hr : r ≤ 0) :
    ((((-r).toNat * 2 ^ 99 : Nat) : Real) / ((QS : Nat) : Real)) =
      -((r : Real) / ((10 ^ 27 : Nat) : Real)) := by
  rw [ray_exp_arg_of_nonneg (r := -r) (by omega)]
  norm_num [Int.cast_neg]
  ring

lemma wadRatio_pos {x : Nat} (hx : 0 < x) : 0 < (x : Real) / ((10 ^ 18 : Nat) : Real) := by
  have hxR : 0 < (x : Real) := by exact_mod_cast hx
  exact div_pos hxR (by norm_num)

lemma wadReciprocal_pos {x : Nat} (hx : 0 < x) : 0 < ((10 ^ 18 : Nat) : Real) / x := by
  have hxR : 0 < (x : Real) := by exact_mod_cast hx
  exact div_pos (by norm_num) hxR

lemma reciprocal_wadRatio {x : Nat} (hx : 0 < x) :
    ((10 ^ 18 : Nat) : Real) / x = ((x : Real) / ((10 ^ 18 : Nat) : Real))⁻¹ := by
  have hxR : (x : Real) ≠ 0 := by exact_mod_cast ne_of_gt hx
  field_simp [hxR]

lemma le_rayLog_of_cutLeLogWadRay {r : Int} {x : Nat} (hx : 0 < x)
    (hcut : CutLeLogWadRay r x) :
    (r : Real) ≤ ((10 ^ 27 : Nat) : Real) * Real.log ((x : Real) / ((10 ^ 18 : Nat) : Real)) := by
  have hRpos : 0 < ((10 ^ 27 : Nat) : Real) := by norm_num
  have hratio : 0 < (x : Real) / ((10 ^ 18 : Nat) : Real) := wadRatio_pos hx
  by_cases hr : 0 ≤ r
  · have hc : capUB (r.toNat * 2 ^ 99) QS x (10 ^ 18) := by
      simpa [CutLeLogWadRay, CutExpLe, hr] using hcut
    have he := exp_le_of_capUB QS_pos (by decide : 0 < (10 ^ 18 : Nat)) hc
    rw [ray_exp_arg_of_nonneg hr] at he
    have hlog : (r : Real) / ((10 ^ 27 : Nat) : Real) ≤
        Real.log ((x : Real) / ((10 ^ 18 : Nat) : Real)) :=
      (Real.le_log_iff_exp_le hratio).mpr he
    have hmul := (div_le_iff₀ hRpos).mp hlog
    nlinarith
  · have hrlt : r < 0 := by omega
    have hc : capLB ((-r).toNat * 2 ^ 99) QS (10 ^ 18) x := by
      simpa [CutLeLogWadRay, CutRatioLeExp, hr] using hcut
    have he := le_exp_of_capLB QS_pos hx hc
    rw [ray_exp_arg_of_neg hrlt] at he
    have hrecpos : 0 < ((10 ^ 18 : Nat) : Real) / x := wadReciprocal_pos hx
    have hlogrec : Real.log (((10 ^ 18 : Nat) : Real) / x) ≤
        -((r : Real) / ((10 ^ 27 : Nat) : Real)) :=
      (Real.log_le_iff_le_exp hrecpos).mpr he
    rw [reciprocal_wadRatio hx, Real.log_inv] at hlogrec
    have hlog : (r : Real) / ((10 ^ 27 : Nat) : Real) ≤
        Real.log ((x : Real) / ((10 ^ 18 : Nat) : Real)) := by
      nlinarith
    have hmul := (div_le_iff₀ hRpos).mp hlog
    nlinarith

lemma wadRatio_lt_upperMargin {x : Nat} (hx : 0 < x) :
    (x : Real) / ((10 ^ 18 : Nat) : Real) <
      ((x * 10 ^ 31 : Nat) : Real) /
        (((10 ^ 18) * (10 ^ 31 - 10) : Nat) : Real) := by
  have hxR : 0 < (x : Real) := by exact_mod_cast hx
  norm_num [Nat.cast_mul, Nat.cast_pow]
  nlinarith [hxR]

lemma lowerMargin_lt_wadReciprocal {x : Nat} (hx : 0 < x) :
    (((10 ^ 18) * (10 ^ 31 - 10) : Nat) : Real) / ((x * 10 ^ 31 : Nat) : Real) <
      ((10 ^ 18 : Nat) : Real) / x := by
  have hxR : 0 < (x : Real) := by exact_mod_cast hx
  norm_num [Nat.cast_mul, Nat.cast_pow]
  have hden : 0 < (x : Real) * 10000000000000000000000000000000 := by positivity
  rw [div_lt_iff₀ hden]
  have hcancel : 1000000000000000000 / (x : Real) *
      ((x : Real) * 10000000000000000000000000000000) =
      1000000000000000000 * 10000000000000000000000000000000 := by
    field_simp [hxR.ne']
    ring
  rw [hcancel]
  norm_num

lemma rayLog_lt_of_cutLogWadRayLtWithMargin {b : Int} {x : Nat} (hx : 0 < x)
    (hcut : CutLogWadRayLtWithMargin x b) :
    ((10 ^ 27 : Nat) : Real) * Real.log ((x : Real) / ((10 ^ 18 : Nat) : Real)) < (b : Real) := by
  have hRpos : 0 < ((10 ^ 27 : Nat) : Real) := by norm_num
  have hratio : 0 < (x : Real) / ((10 ^ 18 : Nat) : Real) := wadRatio_pos hx
  by_cases hb : 1 ≤ b
  · have hb0 : 0 ≤ b := by omega
    have hc : capLB (b.toNat * 2 ^ 99) QS (x * 10 ^ 31) (10 ^ 18 * (10 ^ 31 - 10)) := by
      simpa [CutLogWadRayLtWithMargin, CutRatioLeExp, hb] using hcut
    have he := le_exp_of_capLB QS_pos (by decide : 0 < (10 ^ 18 * (10 ^ 31 - 10) : Nat)) hc
    rw [ray_exp_arg_of_nonneg hb0] at he
    have hmargin := wadRatio_lt_upperMargin hx
    have hlt_exp : (x : Real) / ((10 ^ 18 : Nat) : Real) <
        Real.exp ((b : Real) / ((10 ^ 27 : Nat) : Real)) := lt_of_lt_of_le hmargin he
    have hlog : Real.log ((x : Real) / ((10 ^ 18 : Nat) : Real)) <
        (b : Real) / ((10 ^ 27 : Nat) : Real) :=
      (Real.log_lt_iff_lt_exp hratio).mpr hlt_exp
    have hmul := (lt_div_iff₀' hRpos).mp hlog
    nlinarith
  · have hb0 : b ≤ 0 := by omega
    have hc : capUB ((-b).toNat * 2 ^ 99) QS (10 ^ 18 * (10 ^ 31 - 10)) (x * 10 ^ 31) := by
      simpa [CutLogWadRayLtWithMargin, CutExpLe, hb] using hcut
    have he := exp_le_of_capUB QS_pos (by exact Nat.mul_pos hx (by decide : 0 < (10 ^ 31 : Nat))) hc
    rw [ray_exp_arg_of_nonpos hb0] at he
    have hmargin := lowerMargin_lt_wadReciprocal hx
    have hlt_rec : Real.exp (-((b : Real) / ((10 ^ 27 : Nat) : Real))) <
        ((10 ^ 18 : Nat) : Real) / x := lt_of_le_of_lt he hmargin
    have hrecpos : 0 < ((10 ^ 18 : Nat) : Real) / x := wadReciprocal_pos hx
    have hlogrec : -((b : Real) / ((10 ^ 27 : Nat) : Real)) <
        Real.log (((10 ^ 18 : Nat) : Real) / x) :=
      (Real.lt_log_iff_exp_lt hrecpos).mpr hlt_rec
    rw [reciprocal_wadRatio hx, Real.log_inv] at hlogrec
    have hlog : Real.log ((x : Real) / ((10 ^ 18 : Nat) : Real)) <
        (b : Real) / ((10 ^ 27 : Nat) : Real) := by
      nlinarith
    have hmul := (lt_div_iff₀' hRpos).mp hlog
    nlinarith

lemma cutLnWadRayBracket_real {r : Int} {x : Nat} (hx : 0 < x)
    (hcut : CutLnWadRayBracket r x) : LnRealSpec.LnWadToRaySpec x r := by
  unfold LnRealSpec.LnWadToRaySpec LnRealSpec.lnWadToRayTarget LnRealSpec.wadRatio
  constructor
  · simpa [LnRealSpec.RAY, LnRealSpec.WAD] using le_rayLog_of_cutLeLogWadRay (r := r) (x := x) hx hcut.1
  · simpa [LnRealSpec.RAY, LnRealSpec.WAD, Int.cast_add, Int.cast_ofNat] using
      rayLog_lt_of_cutLogWadRayLtWithMargin (b := r + 2) (x := x) hx hcut.2

lemma cutLnWadSpec_real {ray wad : Int} {x : Nat} (hx : 0 < x)
    (hcut : CutLnWadSpec ray wad x) : LnRealSpec.LnWadSpec x wad := by
  obtain ⟨hrayCut, hfloorlo, hfloorhi⟩ := hcut
  have hray := cutLnWadRayBracket_real (r := ray) (x := x) hx hrayCut
  unfold LnRealSpec.LnWadToRaySpec LnRealSpec.lnWadToRayTarget LnRealSpec.wadRatio at hray
  unfold LnRealSpec.LnWadSpec LnRealSpec.lnWadTarget LnRealSpec.wadRatio
  simp [LnRealSpec.RAY, LnRealSpec.WAD] at hray ⊢
  have hfloorloR : (wad : Real) * (1000000000 : Real) ≤ (ray : Real) := by
    exact_mod_cast hfloorlo
  have hfloorhiR : (ray : Real) < ((wad + 1 : Int) : Real) * (1000000000 : Real) := by
    exact_mod_cast hfloorhi
  constructor
  · have hscale : ((10 ^ 27 : Nat) : Real) = (1000000000 : Real) * ((10 ^ 18 : Nat) : Real) := by
      norm_num
    nlinarith [hray.1, hfloorloR, hscale]
  · have hscale : ((10 ^ 27 : Nat) : Real) = (1000000000 : Real) * ((10 ^ 18 : Nat) : Real) := by
      norm_num
    have hwide : ((wad + 1 : Int) : Real) * (1000000000 : Real) + 2 ≤
        ((wad + 2 : Int) : Real) * (1000000000 : Real) := by
      norm_num [Int.cast_add]
      ring_nf
      linarith
    norm_num [Int.cast_add] at hfloorhiR hwide
    nlinarith [hray.2, hfloorhiR, hwide, hscale]

end

end LnRealBridge
