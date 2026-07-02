import ExpProof.Floor.GranV

/-!
# The exported real-level granularity bounds

The two per-side packagings of the `Floor.GranV` machinery that the `r0`-vs-`exp` chains consume:
one `v`-grid grain lifts `2¹²⁶·ê` by at most `3395595387735630095/10¹⁹` on the `t ≥ 0` half
(never-over side) and by at most `1685843742692980488/10¹⁹` — `Mp`-factor included — on the
`t ≤ 0` half (deficit side); the respective opposite directions are free.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Poly

set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 2000

/-! ## The exported real-level granularity bounds -/

noncomputable section

/-- **Granularity, never-over half (`t ≥ 0`)**: the cert rational never exceeds the grid rational,
and the grid rational exceeds the cert rational by at most one `K`-step:
`2¹²⁶·(ê(v) − ê(t²)) ≤ 3395595387735630095/10¹⁹`. -/
theorem gran_over_pair {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    (evalPoly ExpCertV.numExpV (int256 (tTree x)) : Real) /
        (evalPoly ExpCertV.denExpV (int256 (tTree x)) : Real) ≤
      (NUMv (vTree x) (int256 (tTree x)) : Real) / (DENv (vTree x) (int256 (tTree x)) : Real) ∧
    (2 ^ 126 : Real) * ((NUMv (vTree x) (int256 (tTree x)) : Real) /
        (DENv (vTree x) (int256 (tTree x)) : Real)) ≤
      (2 ^ 126 : Real) * ((evalPoly ExpCertV.numExpV (int256 (tTree x)) : Real) /
        (evalPoly ExpCertV.denExpV (int256 (tTree x)) : Real)) +
        3395595387735630095 / 10000000000000000000 := by
  obtain ⟨htie1, htie2⟩ := tie_over hx hC hC0 htnn
  obtain ⟨_, hthi⟩ := tTree_in_cert_domain hx hC hC0
  have hvle := vTree_le_vmax hx hC hC0
  set t := int256 (tTree x) with htdef
  set v := vTree x with hvdef
  have htdom : t ≤ (ExpCertV.H128 : Int) := by
    rw [show ((ExpCertV.H128 : Nat) : Int) = 117932881612756647068972071382077242199 from by
      unfold ExpCertV.H128; norm_num]
    exact hthi
  -- denominators
  have hD : 554482771859 * 2 ^ 725 ≤ DENv v t := DENv_ge_over (by omega) htnn hthi
  have hD1 : 554482771859 * 2 ^ 725 ≤ DENv (v + 1) t := DENv_ge_over (by omega) htnn hthi
  have hDpos : (0:Int) < DENv v t := lt_of_lt_of_le (by positivity) hD
  have hD1pos : (0:Int) < DENv (v + 1) t := lt_of_lt_of_le (by positivity) hD1
  have hDE : (1:Int) ≤ evalPoly ExpCertV.denExpV t := certDE_pos htnn htdom
  have hDEpos : (0:Int) < evalPoly ExpCertV.denExpV t := lt_of_lt_of_le one_pos hDE
  have hDR : (0:Real) < (DENv v t : Real) := by exact_mod_cast hDpos
  have hD1R : (0:Real) < (DENv (v + 1) t : Real) := by exact_mod_cast hD1pos
  have hDER : (0:Real) < (evalPoly ExpCertV.denExpV t : Real) := by exact_mod_cast hDEpos
  -- part 1: NE/DE ≤ NUMv/DENv (cross form htie1)
  have hpart1 : (evalPoly ExpCertV.numExpV t : Real) / (evalPoly ExpCertV.denExpV t : Real) ≤
      (NUMv v t : Real) / (DENv v t : Real) := by
    rw [div_le_div_iff₀ hDER hDR]
    exact_mod_cast htie1
  refine ⟨hpart1, ?_⟩
  -- part 2: Qv − Qw ≤ Qv − Qv1 = one K-step ≤ budget/2^126
  have hQv1_le_Qw : (NUMv (v + 1) t : Real) / (DENv (v + 1) t : Real) ≤
      (evalPoly ExpCertV.numExpV t : Real) / (evalPoly ExpCertV.denExpV t : Real) := by
    rw [div_le_div_iff₀ hD1R hDER]
    exact_mod_cast htie2
  have hstep_eq : (NUMv v t : Real) / (DENv v t : Real) -
      (NUMv (v + 1) t : Real) / (DENv (v + 1) t : Real) =
      ((2 * t * 2 ^ 110 * KpM v : Int) : Real) /
        ((DENv v t : Real) * (DENv (v + 1) t : Real)) := by
    rw [div_sub_div _ _ (ne_of_gt hDR) (ne_of_gt hD1R)]
    congr 1
    have hid := step_identity v t
    have hcast : ((NUMv v t : Int) : Real) * ((DENv (v + 1) t : Int) : Real) -
        ((DENv v t : Int) : Real) * ((NUMv (v + 1) t : Int) : Real) =
        ((2 * t * 2 ^ 110 * KpM v : Int) : Real) := by
      rw [show ((2 * t * 2 ^ 110 * KpM v : Int) : Real) =
          ((NUMv v t * DENv (v + 1) t - NUMv (v + 1) t * DENv v t : Int) : Real) from by
        exact_mod_cast (congrArg (fun z : Int => (z : Real)) hid.symm)]
      push_cast
      ring
    exact hcast
  -- numerator and denominator bounds for the K-step
  have hKnn := KpM_nonneg v
  have hKle := KpM_le_KVMAX hvle
  have hnum_nn : (0:Int) ≤ 2 * t * 2 ^ 110 * KpM v := by positivity
  have hnum_le : 2 * t * 2 ^ 110 * KpM v ≤
      2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KVMAXc := by
    have h1 : 2 * t * 2 ^ 110 * KpM v ≤
        2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KpM v := by
      have hcoef : 2 * t * 2 ^ 110 ≤ 2 * 117932881612756647068972071382077242199 * 2 ^ 110 := by
        nlinarith [hthi]
      exact mul_le_mul_of_nonneg_right hcoef hKnn
    have h2 : 2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KpM v ≤
        2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KVMAXc :=
      mul_le_mul_of_nonneg_left hKle (by positivity)
    linarith [h1, h2]
  have hden_ge : (554482771859 * 2 ^ 725 : Real) * (554482771859 * 2 ^ 725 : Real) ≤
      (DENv v t : Real) * (DENv (v + 1) t : Real) := by
    have hDRc : (554482771859 * 2 ^ 725 : Real) ≤ (DENv v t : Real) := by exact_mod_cast hD
    have hD1Rc : (554482771859 * 2 ^ 725 : Real) ≤ (DENv (v + 1) t : Real) := by exact_mod_cast hD1
    exact mul_le_mul hDRc hD1Rc (by positivity) (le_of_lt hDR)
  -- the K-step fraction is inside the budget
  have hfrac : ((2 * t * 2 ^ 110 * KpM v : Int) : Real) /
      ((DENv v t : Real) * (DENv (v + 1) t : Real)) ≤
      3395595387735630095 / 10000000000000000000 / 2 ^ 126 := by
    have hdd : (0:Real) < (DENv v t : Real) * (DENv (v + 1) t : Real) := mul_pos hDR hD1R
    rw [div_le_div_iff₀ hdd (by positivity : (0:Real) < (2:Real) ^ 126)]
    have hnumR : ((2 * t * 2 ^ 110 * KpM v : Int) : Real) ≤
        ((2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KVMAXc : Int) : Real) := by
      exact_mod_cast hnum_le
    have h1 : ((2 * t * 2 ^ 110 * KpM v : Int) : Real) * 2 ^ 126 ≤
        ((2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KVMAXc : Int) : Real) * 2 ^ 126 :=
      mul_le_mul_of_nonneg_right hnumR (by positivity)
    have h2 : ((2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KVMAXc : Int) : Real) *
        2 ^ 126 ≤ (3395595387735630095 / 10000000000000000000 : Real) *
          ((554482771859 * 2 ^ 725 : Real) * (554482771859 * 2 ^ 725 : Real)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0:Real) < 10000000000000000000)]
      have hint : (2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KVMAXc : Int) *
          2 ^ 126 * 10000000000000000000 ≤ (3395595387735630095 : Int) *
            ((554482771859 * 2 ^ 725) * (554482771859 * 2 ^ 725)) := by
        unfold KVMAXc
        norm_num
      exact_mod_cast hint
    have h3 : (3395595387735630095 / 10000000000000000000 : Real) *
        ((554482771859 * 2 ^ 725 : Real) * (554482771859 * 2 ^ 725 : Real)) ≤
        (3395595387735630095 / 10000000000000000000 : Real) *
          ((DENv v t : Real) * (DENv (v + 1) t : Real)) :=
      mul_le_mul_of_nonneg_left hden_ge (by positivity)
    exact le_trans h1 (le_trans h2 h3)
  -- assemble part 2
  have hQvQw : (NUMv v t : Real) / (DENv v t : Real) -
      (evalPoly ExpCertV.numExpV t : Real) / (evalPoly ExpCertV.denExpV t : Real) ≤
      3395595387735630095 / 10000000000000000000 / 2 ^ 126 := by
    linarith [hstep_eq, hfrac, hQv1_le_Qw]
  have h2126 := mul_le_mul_of_nonneg_left hQvQw (by positivity : (0:Real) ≤ (2:Real) ^ 126)
  have hcancel : (2:Real) ^ 126 * (3395595387735630095 / 10000000000000000000 / 2 ^ 126) =
      3395595387735630095 / 10000000000000000000 := by
    norm_num
  rw [hcancel] at h2126
  linarith [h2126]

/-- **Granularity, deficit half (`t ≤ 0`)**: the grid rational never exceeds the cert rational, and
the cert rational exceeds the grid rational — `Mp`-factor `2¹³¹/(2¹³¹−1)` included — by at most
`1685843742692980488/10¹⁹` after scaling by `2¹²⁶`. The one-grain lift is monotone in `|t|`
(the sign condition is the over-half denominator floor), so the `t = −H128` denominator floor
`certDUnder` applies for every `t` in the half. -/
theorem gran_under_pair {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnp : int256 (tTree x) ≤ 0) :
    (NUMv (vTree x) (int256 (tTree x)) : Real) / (DENv (vTree x) (int256 (tTree x)) : Real) ≤
      (evalPoly ExpCertV.numExpV (int256 (tTree x)) : Real) /
        (evalPoly ExpCertV.denExpV (int256 (tTree x)) : Real) ∧
    (2 ^ 126 : Real) * ((2 ^ 131 : Real) / ((2 ^ 131 : Real) - 1)) *
        ((evalPoly ExpCertV.numExpV (int256 (tTree x)) : Real) /
          (evalPoly ExpCertV.denExpV (int256 (tTree x)) : Real) -
         (NUMv (vTree x) (int256 (tTree x)) : Real) / (DENv (vTree x) (int256 (tTree x)) : Real)) ≤
      1685843742692980488 / 10000000000000000000 := by
  obtain ⟨htie1, htie2⟩ := tie_under hx hC hC0 htnp
  obtain ⟨htlo, _⟩ := tTree_in_cert_domain hx hC hC0
  have hvle := vTree_le_vmax hx hC hC0
  set t := int256 (tTree x) with htdef
  set v := vTree x with hvdef
  have hntH : -t ≤ 117932881612756647068972071382077242199 := by linarith [htlo]
  have htdom : -t ≤ (ExpCertV.H128 : Int) := by
    rw [show ((ExpCertV.H128 : Nat) : Int) = 117932881612756647068972071382077242199 from by
      unfold ExpCertV.H128; norm_num]
    exact hntH
  -- denominators
  have hD : 554482771859 * 2 ^ 725 ≤ DENv v t := DENv_ge_neg (by omega) htnp
  have hD1 : 554482771859 * 2 ^ 725 ≤ DENv (v + 1) t := DENv_ge_neg (by omega) htnp
  have hDpos : (0:Int) < DENv v t := lt_of_lt_of_le (by positivity) hD
  have hD1pos : (0:Int) < DENv (v + 1) t := lt_of_lt_of_le (by positivity) hD1
  have hDEpos : (0:Int) < evalPoly ExpCertV.denExpV t := (certNE_pos_neg_aux htnp htdom).2
  have hDR : (0:Real) < (DENv v t : Real) := by exact_mod_cast hDpos
  have hD1R : (0:Real) < (DENv (v + 1) t : Real) := by exact_mod_cast hD1pos
  have hDER : (0:Real) < (evalPoly ExpCertV.denExpV t : Real) := by exact_mod_cast hDEpos
  -- part 1: NUMv/DENv ≤ NE/DE
  have hpart1 : (NUMv v t : Real) / (DENv v t : Real) ≤
      (evalPoly ExpCertV.numExpV t : Real) / (evalPoly ExpCertV.denExpV t : Real) := by
    rw [div_le_div_iff₀ hDR hDER]
    exact_mod_cast htie1
  refine ⟨hpart1, ?_⟩
  -- part 2: Qw − Qv ≤ Qv1 − Qv = one K-step, |t|-monotone, floored at t = −H128
  have hQw_le_Qv1 : (evalPoly ExpCertV.numExpV t : Real) / (evalPoly ExpCertV.denExpV t : Real) ≤
      (NUMv (v + 1) t : Real) / (DENv (v + 1) t : Real) := by
    rw [div_le_div_iff₀ hDER hD1R]
    exact_mod_cast htie2
  have hstep_eq : (NUMv (v + 1) t : Real) / (DENv (v + 1) t : Real) -
      (NUMv v t : Real) / (DENv v t : Real) =
      ((2 * (-t) * 2 ^ 110 * KpM v : Int) : Real) /
        ((DENv (v + 1) t : Real) * (DENv v t : Real)) := by
    rw [div_sub_div _ _ (ne_of_gt hD1R) (ne_of_gt hDR)]
    congr 1
    have hid := step_identity v t
    have hswap : NUMv (v + 1) t * DENv v t - DENv (v + 1) t * NUMv v t =
        2 * (-t) * 2 ^ 110 * KpM v := by linear_combination -hid
    rw [show ((2 * (-t) * 2 ^ 110 * KpM v : Int) : Real) =
        ((NUMv (v + 1) t * DENv v t - DENv (v + 1) t * NUMv v t : Int) : Real) from by
      exact_mod_cast (congrArg (fun z : Int => (z : Real)) hswap.symm)]
    push_cast
    ring
  -- the |t|-monotonicity: u·D(H)·D′(H) ≤ H·D(u)·D′(u) with u = −t ≤ H
  set u : Int := -t with hudef
  have hu0 : (0:Int) ≤ u := by rw [hudef]; linarith [htnp]
  set A : Int := (evNumV v : Int) * 2 ^ 110 with hAdef
  set Bo : Int := (odNumV v : Int) with hBodef
  set A1 : Int := (evNumV (v + 1) : Int) * 2 ^ 110 with hA1def
  set Bo1 : Int := (odNumV (v + 1) : Int) with hBo1def
  have hBo_nn : (0:Int) ≤ Bo := Int.natCast_nonneg _
  have hBo1_nn : (0:Int) ≤ Bo1 := Int.natCast_nonneg _
  have hAB : 117932881612756647068972071382077242199 * Bo ≤ A := HOd_le_Ev (by omega)
  have hA1B1 : 117932881612756647068972071382077242199 * Bo1 ≤ A1 := HOd_le_Ev (by omega)
  have hDu : DENv v t = A + u * Bo := by unfold DENv; rw [hAdef, hBodef, hudef]; ring
  have hDu1 : DENv (v + 1) t = A1 + u * Bo1 := by
    unfold DENv; rw [hA1def, hBo1def, hudef]; ring
  have hmono : u * ((A + 117932881612756647068972071382077242199 * Bo) *
      (A1 + 117932881612756647068972071382077242199 * Bo1)) ≤
      117932881612756647068972071382077242199 * ((A + u * Bo) * (A1 + u * Bo1)) := by
    have hid : 117932881612756647068972071382077242199 * ((A + u * Bo) * (A1 + u * Bo1)) -
        u * ((A + 117932881612756647068972071382077242199 * Bo) *
          (A1 + 117932881612756647068972071382077242199 * Bo1)) =
        (117932881612756647068972071382077242199 - u) *
          (A * A1 - 117932881612756647068972071382077242199 * u * (Bo * Bo1)) := by ring
    have hprod : 117932881612756647068972071382077242199 * u * (Bo * Bo1) ≤ A * A1 := by
      have h1 : 117932881612756647068972071382077242199 * u * (Bo * Bo1) ≤
          117932881612756647068972071382077242199 *
            117932881612756647068972071382077242199 * (Bo * Bo1) := by
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hntH
            (by norm_num : (0:Int) ≤ 117932881612756647068972071382077242199))
          (mul_nonneg hBo_nn hBo1_nn)
        linarith [this]
      have h2 : (117932881612756647068972071382077242199 *
          117932881612756647068972071382077242199 * (Bo * Bo1) : Int) =
          (117932881612756647068972071382077242199 * Bo) *
            (117932881612756647068972071382077242199 * Bo1) := by ring
      have h3 : (117932881612756647068972071382077242199 * Bo) *
          (117932881612756647068972071382077242199 * Bo1) ≤ A * A1 :=
        mul_le_mul hAB hA1B1
          (mul_nonneg (by norm_num) hBo1_nn)
          (le_trans (mul_nonneg (by norm_num) hBo_nn) hAB)
      linarith [h1, h2 ▸ h1, h3]
    have hfac1 : (0:Int) ≤ 117932881612756647068972071382077242199 - u := by
      rw [hudef]; linarith [hntH]
    have hfac2 : (0:Int) ≤ A * A1 - 117932881612756647068972071382077242199 * u * (Bo * Bo1) := by
      linarith [hprod]
    linarith only [mul_nonneg hfac1 hfac2, hid]
  -- floor the H128-denominators with the under certificate
  have hDH : 786932288647 * 2 ^ 725 ≤ A + 117932881612756647068972071382077242199 * Bo := by
    have := D_at_H_ge_under (v := v) (by omega)
    rw [hAdef, hBodef]; linarith [this]
  have hDH1 : 786932288647 * 2 ^ 725 ≤ A1 + 117932881612756647068972071382077242199 * Bo1 := by
    have := D_at_H_ge_under (v := v + 1) (by omega)
    rw [hA1def, hBo1def]; linarith [this]
  have hDHpos : (0:Int) < A + 117932881612756647068972071382077242199 * Bo :=
    lt_of_lt_of_le (by positivity) hDH
  have hDH1pos : (0:Int) < A1 + 117932881612756647068972071382077242199 * Bo1 :=
    lt_of_lt_of_le (by positivity) hDH1
  have hKnn := KpM_nonneg v
  have hKle := KpM_le_KVMAX hvle
  -- the fraction chain: u-step ≤ H-step ≤ literal maximum
  have hfracu : ((2 * u * 2 ^ 110 * KpM v : Int) : Real) /
      ((DENv (v + 1) t : Real) * (DENv v t : Real)) ≤
      ((2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KpM v : Int) : Real) /
        (((A1 + 117932881612756647068972071382077242199 * Bo1 : Int) : Real) *
         ((A + 117932881612756647068972071382077242199 * Bo : Int) : Real)) := by
    have hdd : (0:Real) < (DENv (v + 1) t : Real) * (DENv v t : Real) := mul_pos hD1R hDR
    have hdH : (0:Real) < ((A1 + 117932881612756647068972071382077242199 * Bo1 : Int) : Real) *
        ((A + 117932881612756647068972071382077242199 * Bo : Int) : Real) := by
      have h1 : (0:Real) < ((A1 + 117932881612756647068972071382077242199 * Bo1 : Int) : Real) := by
        exact_mod_cast hDH1pos
      have h2 : (0:Real) < ((A + 117932881612756647068972071382077242199 * Bo : Int) : Real) := by
        exact_mod_cast hDHpos
      exact mul_pos h1 h2
    rw [div_le_div_iff₀ hdd hdH]
    -- cross-multiplied: (2u·2^110·Kp)·(D1(H)·D(H)) ≤ (2H·2^110·Kp)·(D1(u)·D(u))
    have hint : (2 * u * 2 ^ 110 * KpM v) *
        ((A1 + 117932881612756647068972071382077242199 * Bo1) *
         (A + 117932881612756647068972071382077242199 * Bo)) ≤
        (2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KpM v) *
          ((A1 + u * Bo1) * (A + u * Bo)) := by
      have hc : (0:Int) ≤ 2 * 2 ^ 110 * KpM v :=
        mul_nonneg (by norm_num) hKnn
      have hscaled := mul_le_mul_of_nonneg_left hmono hc
      linarith only [hscaled]
    have hrw : (DENv (v + 1) t : Real) * (DENv v t : Real) =
        (((A1 + u * Bo1) * (A + u * Bo) : Int) : Real) := by
      rw [hDu, hDu1]; push_cast; ring
    rw [hrw]
    calc ((2 * u * 2 ^ 110 * KpM v : Int) : Real) *
          (((A1 + 117932881612756647068972071382077242199 * Bo1 : Int) : Real) *
           ((A + 117932881612756647068972071382077242199 * Bo : Int) : Real))
        = (((2 * u * 2 ^ 110 * KpM v) *
            ((A1 + 117932881612756647068972071382077242199 * Bo1) *
             (A + 117932881612756647068972071382077242199 * Bo)) : Int) : Real) := by
          push_cast; ring
      _ ≤ (((2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KpM v) *
            ((A1 + u * Bo1) * (A + u * Bo)) : Int) : Real) := by exact_mod_cast hint
      _ = ((2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KpM v : Int) : Real) *
            (((A1 + u * Bo1) * (A + u * Bo) : Int) : Real) := by push_cast; ring
  have hfracH : ((2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KpM v : Int) : Real) /
      (((A1 + 117932881612756647068972071382077242199 * Bo1 : Int) : Real) *
       ((A + 117932881612756647068972071382077242199 * Bo : Int) : Real)) ≤
      ((2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KVMAXc : Int) : Real) /
        ((786932288647 * 2 ^ 725 : Real) * (786932288647 * 2 ^ 725 : Real)) := by
    have hdH : (0:Real) < ((A1 + 117932881612756647068972071382077242199 * Bo1 : Int) : Real) *
        ((A + 117932881612756647068972071382077242199 * Bo : Int) : Real) := by
      have h1 : (0:Real) < ((A1 + 117932881612756647068972071382077242199 * Bo1 : Int) : Real) := by
        exact_mod_cast hDH1pos
      have h2 : (0:Real) < ((A + 117932881612756647068972071382077242199 * Bo : Int) : Real) := by
        exact_mod_cast hDHpos
      exact mul_pos h1 h2
    rw [div_le_div_iff₀ hdH (by positivity)]
    have hnum : ((2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KpM v : Int) : Real) ≤
        ((2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KVMAXc : Int) : Real) := by
      have : (2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KpM v : Int) ≤
          2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KVMAXc :=
        mul_le_mul_of_nonneg_left hKle (by positivity)
      exact_mod_cast this
    have hnum_nn : (0:Real) ≤
        ((2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KpM v : Int) : Real) := by
      have : (0:Int) ≤ 2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KpM v :=
        mul_nonneg (by norm_num) hKnn
      exact_mod_cast this
    have hden : ((786932288647 * 2 ^ 725 : Real) * (786932288647 * 2 ^ 725 : Real)) ≤
        ((A1 + 117932881612756647068972071382077242199 * Bo1 : Int) : Real) *
          ((A + 117932881612756647068972071382077242199 * Bo : Int) : Real) := by
      have h1 : (786932288647 * 2 ^ 725 : Real) ≤
          ((A1 + 117932881612756647068972071382077242199 * Bo1 : Int) : Real) := by
        exact_mod_cast hDH1
      have h2 : (786932288647 * 2 ^ 725 : Real) ≤
          ((A + 117932881612756647068972071382077242199 * Bo : Int) : Real) := by
        exact_mod_cast hDH
      exact mul_le_mul h1 h2 (by positivity) (by exact_mod_cast le_of_lt hDH1pos)
    calc ((2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KpM v : Int) : Real) *
          ((786932288647 * 2 ^ 725 : Real) * (786932288647 * 2 ^ 725 : Real))
        ≤ ((2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KVMAXc : Int) : Real) *
          ((786932288647 * 2 ^ 725 : Real) * (786932288647 * 2 ^ 725 : Real)) :=
          mul_le_mul_of_nonneg_right hnum (by positivity)
      _ ≤ ((2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KVMAXc : Int) : Real) *
          (((A1 + 117932881612756647068972071382077242199 * Bo1 : Int) : Real) *
           ((A + 117932881612756647068972071382077242199 * Bo : Int) : Real)) := by
          apply mul_le_mul_of_nonneg_left hden
          exact le_trans hnum_nn hnum
  -- the literal budget, Mp-factor included
  have hbudget : (2 ^ 126 : Real) * ((2 ^ 131 : Real) / ((2 ^ 131 : Real) - 1)) *
      (((2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KVMAXc : Int) : Real) /
        ((786932288647 * 2 ^ 725 : Real) * (786932288647 * 2 ^ 725 : Real))) ≤
      1685843742692980488 / 10000000000000000000 := by
    have hMp1 : (0:Real) < (2 ^ 131 : Real) - 1 := by norm_num
    have hDD : (0:Real) < (786932288647 * 2 ^ 725 : Real) * (786932288647 * 2 ^ 725 : Real) := by
      positivity
    rw [show (2 ^ 126 : Real) * ((2 ^ 131 : Real) / ((2 ^ 131 : Real) - 1)) *
        (((2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KVMAXc : Int) : Real) /
          ((786932288647 * 2 ^ 725 : Real) * (786932288647 * 2 ^ 725 : Real))) =
        ((2 ^ 126 * 2 ^ 131 : Real) *
          ((2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KVMAXc : Int) : Real)) /
          ((((2 ^ 131 : Real) - 1)) *
            ((786932288647 * 2 ^ 725 : Real) * (786932288647 * 2 ^ 725 : Real))) from by
      field_simp
      try ring]
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:Real) < 10000000000000000000)]
    have hint : (2 ^ 126 * 2 ^ 131 : Int) *
        (2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KVMAXc) *
        10000000000000000000 ≤ (1685843742692980488 : Int) *
          ((2 ^ 131 - 1) * ((786932288647 * 2 ^ 725) * (786932288647 * 2 ^ 725))) := by
      unfold KVMAXc
      norm_num
    calc (2 ^ 126 * 2 ^ 131 : Real) *
          ((2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KVMAXc : Int) : Real) *
          10000000000000000000
        = (((2 ^ 126 * 2 ^ 131 : Int) *
            (2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KVMAXc) *
            10000000000000000000 : Int) : Real) := by push_cast; ring
      _ ≤ (((1685843742692980488 : Int) *
            ((2 ^ 131 - 1) * ((786932288647 * 2 ^ 725) * (786932288647 * 2 ^ 725))) : Int) : Real) := by
          exact_mod_cast hint
      _ = (1685843742692980488 : Real) *
            (((2 ^ 131 : Real) - 1) *
              ((786932288647 * 2 ^ 725 : Real) * (786932288647 * 2 ^ 725 : Real))) := by
          push_cast; ring
  -- assemble part 2
  have hgap_le : (evalPoly ExpCertV.numExpV t : Real) / (evalPoly ExpCertV.denExpV t : Real) -
      (NUMv v t : Real) / (DENv v t : Real) ≤
      ((2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KVMAXc : Int) : Real) /
        ((786932288647 * 2 ^ 725 : Real) * (786932288647 * 2 ^ 725 : Real)) := by
    have hu_eq : ((2 * u * 2 ^ 110 * KpM v : Int) : Real) =
        ((2 * (-t) * 2 ^ 110 * KpM v : Int) : Real) := by rw [hudef]
    calc (evalPoly ExpCertV.numExpV t : Real) / (evalPoly ExpCertV.denExpV t : Real) -
          (NUMv v t : Real) / (DENv v t : Real)
        ≤ (NUMv (v + 1) t : Real) / (DENv (v + 1) t : Real) -
          (NUMv v t : Real) / (DENv v t : Real) := by linarith [hQw_le_Qv1]
      _ = ((2 * (-t) * 2 ^ 110 * KpM v : Int) : Real) /
          ((DENv (v + 1) t : Real) * (DENv v t : Real)) := hstep_eq
      _ = ((2 * u * 2 ^ 110 * KpM v : Int) : Real) /
          ((DENv (v + 1) t : Real) * (DENv v t : Real)) := by rw [hu_eq]
      _ ≤ ((2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KpM v : Int) : Real) /
          (((A1 + 117932881612756647068972071382077242199 * Bo1 : Int) : Real) *
           ((A + 117932881612756647068972071382077242199 * Bo : Int) : Real)) := hfracu
      _ ≤ ((2 * 117932881612756647068972071382077242199 * 2 ^ 110 * KVMAXc : Int) : Real) /
          ((786932288647 * 2 ^ 725 : Real) * (786932288647 * 2 ^ 725 : Real)) := hfracH
  have hMpnn : (0:Real) ≤ (2 ^ 126 : Real) * ((2 ^ 131 : Real) / ((2 ^ 131 : Real) - 1)) := by
    have : (0:Real) < (2 ^ 131 : Real) - 1 := by norm_num
    positivity
  exact le_trans (mul_le_mul_of_nonneg_left hgap_le hMpnn) hbudget

end

end ExpYul
