import ExpProof.Floor.GranV

/-!
# The exported real-level granularity bounds

The two per-side packagings of the `Floor.GranV` machinery that the `r0`-vs-`exp` chains consume:
one `v`-grid grain lifts `2¹²⁶·ê` by at most `3290521163436398582/10¹⁹` on the `t ≥ 0` half
(never-over side) and by at most `1644901622230542074/10¹⁹` — `Mp`-factor included — on the
`t ≤ 0` half (deficit side); the respective opposite directions are free. Each bound is the
piecewise maximum of the 32 certified per-piece envelopes (`piece_select`): the runtime `v` picks
its piece, whose `t`-cap `T` bounds `|t|`, whose floors bound the two step denominators, and whose
budget inequality bounds the one-`K`-step lift.
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
`2¹²⁶·(ê(v) − ê(t²)) ≤ 3290521163436398582/10¹⁹` (the piecewise-certified envelope). -/
theorem gran_over_pair {x : Nat} (hx : x < 2 ^ 256)
    (hW : WideRegion x)
    (htnn : 0 ≤ int256 (tTree x)) :
    (evalPoly ExpCertV.numExpV (int256 (tTree x)) : Real) /
        (evalPoly ExpCertV.denExpV (int256 (tTree x)) : Real) ≤
      (NUMv (vTree x) (int256 (tTree x)) : Real) / (DENv (vTree x) (int256 (tTree x)) : Real) ∧
    (2 ^ 126 : Real) * ((NUMv (vTree x) (int256 (tTree x)) : Real) /
        (DENv (vTree x) (int256 (tTree x)) : Real)) ≤
      (2 ^ 126 : Real) * ((evalPoly ExpCertV.numExpV (int256 (tTree x)) : Real) /
        (evalPoly ExpCertV.denExpV (int256 (tTree x)) : Real)) +
        3290521163436398582 / 10000000000000000000 := by
  obtain ⟨htie1, htie2⟩ := tie_over_wide hx hW htnn
  obtain ⟨T, DO, DU, Khi, hpiece, hT2⟩ := piece_select_wide hx hW
  obtain ⟨hDOpos, _, hKhinn, hTnn, hflO, hflO1, _, _, hK, hbudO, _⟩ := hpiece
  obtain ⟨_, hthi⟩ := tTree_in_cert_domain_wide hx hW
  set t := int256 (tTree x) with htdef
  set v := vTree x with hvdef
  have htdom : t ≤ (ExpCertV.H129 : Int) := by
    rw [show ((ExpCertV.H129 : Nat) : Int) = 235865763225513294137944142764154484399 from by
      unfold ExpCertV.H129; norm_num]
    exact hthi
  -- the piece cap dominates on this half: t ≤ T
  have htT : t ≤ T := by
    by_contra hgt
    push_neg at hgt
    nlinarith [hT2, htnn, hTnn, hgt]
  -- denominator floors at the runtime t
  have hOd_nn : (0 : Int) ≤ (odNumV v : Int) := Int.natCast_nonneg _
  have hOd1_nn : (0 : Int) ≤ (odNumV (v + 1) : Int) := Int.natCast_nonneg _
  have hD : DO * 2 ^ 725 ≤ DENv v t := by
    have h := mul_le_mul_of_nonneg_right htT hOd_nn
    unfold DENv; linarith [hflO, h]
  have hD1 : DO * 2 ^ 725 ≤ DENv (v + 1) t := by
    have h := mul_le_mul_of_nonneg_right htT hOd1_nn
    unfold DENv; linarith [hflO1, h]
  have hDO725 : (0:Int) < DO * 2 ^ 725 := mul_pos hDOpos (by positivity)
  have hDpos : (0:Int) < DENv v t := lt_of_lt_of_le hDO725 hD
  have hD1pos : (0:Int) < DENv (v + 1) t := lt_of_lt_of_le hDO725 hD1
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
      ((2 * t * 2 ^ 111 * KpM v : Int) : Real) /
        ((DENv v t : Real) * (DENv (v + 1) t : Real)) := by
    rw [div_sub_div _ _ (ne_of_gt hDR) (ne_of_gt hD1R)]
    congr 1
    have hid := step_identity v t
    have hcast : ((NUMv v t : Int) : Real) * ((DENv (v + 1) t : Int) : Real) -
        ((DENv v t : Int) : Real) * ((NUMv (v + 1) t : Int) : Real) =
        ((2 * t * 2 ^ 111 * KpM v : Int) : Real) := by
      rw [show ((2 * t * 2 ^ 111 * KpM v : Int) : Real) =
          ((NUMv v t * DENv (v + 1) t - NUMv (v + 1) t * DENv v t : Int) : Real) from by
        exact_mod_cast (congrArg (fun z : Int => (z : Real)) hid.symm)]
      push_cast
      ring
    exact hcast
  -- numerator and denominator bounds for the K-step
  have hKnn := KpM_nonneg v
  have hnum_le : 2 * t * 2 ^ 111 * KpM v ≤ 2 * T * 2 ^ 111 * Khi := by
    have h1 : 2 * t * 2 ^ 111 * KpM v ≤ 2 * T * 2 ^ 111 * KpM v := by
      have hcoef : 2 * t * 2 ^ 111 ≤ 2 * T * 2 ^ 111 := by nlinarith [htT]
      exact mul_le_mul_of_nonneg_right hcoef hKnn
    have hTc : (0:Int) ≤ 2 * T * 2 ^ 111 :=
      mul_nonneg (mul_nonneg (by norm_num) hTnn) (by norm_num)
    have h2 : 2 * T * 2 ^ 111 * KpM v ≤ 2 * T * 2 ^ 111 * Khi :=
      mul_le_mul_of_nonneg_left hK hTc
    linarith [h1, h2]
  have hden_ge : ((DO * 2 ^ 725 : Int) : Real) * ((DO * 2 ^ 725 : Int) : Real) ≤
      (DENv v t : Real) * (DENv (v + 1) t : Real) := by
    have hDRc : ((DO * 2 ^ 725 : Int) : Real) ≤ (DENv v t : Real) := by exact_mod_cast hD
    have hD1Rc : ((DO * 2 ^ 725 : Int) : Real) ≤ (DENv (v + 1) t : Real) := by exact_mod_cast hD1
    have hDOR : (0:Real) ≤ ((DO * 2 ^ 725 : Int) : Real) := by
      exact_mod_cast le_of_lt hDO725
    exact mul_le_mul hDRc hD1Rc hDOR (le_of_lt hDR)
  -- the K-step fraction is inside the piece budget
  have hfrac : ((2 * t * 2 ^ 111 * KpM v : Int) : Real) /
      ((DENv v t : Real) * (DENv (v + 1) t : Real)) ≤
      3290521163436398582 / 10000000000000000000 / 2 ^ 126 := by
    have hdd : (0:Real) < (DENv v t : Real) * (DENv (v + 1) t : Real) := mul_pos hDR hD1R
    rw [div_le_div_iff₀ hdd (by positivity : (0:Real) < (2:Real) ^ 126)]
    have hnumR : ((2 * t * 2 ^ 111 * KpM v : Int) : Real) ≤
        ((2 * T * 2 ^ 111 * Khi : Int) : Real) := by
      exact_mod_cast hnum_le
    have h1 : ((2 * t * 2 ^ 111 * KpM v : Int) : Real) * 2 ^ 126 ≤
        ((2 * T * 2 ^ 111 * Khi : Int) : Real) * 2 ^ 126 :=
      mul_le_mul_of_nonneg_right hnumR (by positivity)
    have h2 : ((2 * T * 2 ^ 111 * Khi : Int) : Real) * 2 ^ 126 ≤
        (3290521163436398582 / 10000000000000000000 : Real) *
          (((DO * 2 ^ 725 : Int) : Real) * ((DO * 2 ^ 725 : Int) : Real)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0:Real) < 10000000000000000000)]
      exact_mod_cast hbudO
    have h3 : (3290521163436398582 / 10000000000000000000 : Real) *
        (((DO * 2 ^ 725 : Int) : Real) * ((DO * 2 ^ 725 : Int) : Real)) ≤
        (3290521163436398582 / 10000000000000000000 : Real) *
          ((DENv v t : Real) * (DENv (v + 1) t : Real)) :=
      mul_le_mul_of_nonneg_left hden_ge (by positivity)
    exact le_trans h1 (le_trans h2 h3)
  -- assemble part 2
  have hQvQw : (NUMv v t : Real) / (DENv v t : Real) -
      (evalPoly ExpCertV.numExpV t : Real) / (evalPoly ExpCertV.denExpV t : Real) ≤
      3290521163436398582 / 10000000000000000000 / 2 ^ 126 := by
    linarith [hstep_eq, hfrac, hQv1_le_Qw]
  have h2126 := mul_le_mul_of_nonneg_left hQvQw (by positivity : (0:Real) ≤ (2:Real) ^ 126)
  have hcancel : (2:Real) ^ 126 * (3290521163436398582 / 10000000000000000000 / 2 ^ 126) =
      3290521163436398582 / 10000000000000000000 := by
    norm_num
  rw [hcancel] at h2126
  linarith [h2126]

/-- **Granularity, deficit half (`t ≤ 0`)**: the grid rational never exceeds the cert rational, and
the cert rational exceeds the grid rational — `Mp`-factor `2¹³¹/(2¹³¹−1)` included — by at most
`1644901622230542074/10¹⁹` after scaling by `2¹²⁶` (the piecewise-certified envelope). The
one-grain lift is monotone in `|t|` (the sign condition is the over-half denominator floor), so
each piece's `t = −T` denominator floor applies for every `t` in the half. -/
theorem gran_under_pair {x : Nat} (hx : x < 2 ^ 256)
    (hW : WideRegion x)
    (htnp : int256 (tTree x) ≤ 0) :
    (NUMv (vTree x) (int256 (tTree x)) : Real) / (DENv (vTree x) (int256 (tTree x)) : Real) ≤
      (evalPoly ExpCertV.numExpV (int256 (tTree x)) : Real) /
        (evalPoly ExpCertV.denExpV (int256 (tTree x)) : Real) ∧
    (2 ^ 126 : Real) * ((2 ^ 131 : Real) / ((2 ^ 131 : Real) - 1)) *
        ((evalPoly ExpCertV.numExpV (int256 (tTree x)) : Real) /
          (evalPoly ExpCertV.denExpV (int256 (tTree x)) : Real) -
         (NUMv (vTree x) (int256 (tTree x)) : Real) / (DENv (vTree x) (int256 (tTree x)) : Real)) ≤
      1644901622230542074 / 10000000000000000000 := by
  obtain ⟨htie1, htie2⟩ := tie_under_wide hx hW htnp
  obtain ⟨T, DO, DU, Khi, hpiece, hT2⟩ := piece_select_wide hx hW
  obtain ⟨hDOpos, hDUpos, hKhinn, hTnn, hflO, hflO1, hflU, hflU1, hK, _, hbudU⟩ := hpiece
  obtain ⟨htlo, _⟩ := tTree_in_cert_domain_wide hx hW
  have hvle := vTree_le_vmax_wide hx hW
  set t := int256 (tTree x) with htdef
  set v := vTree x with hvdef
  have htdom : -t ≤ (ExpCertV.H129 : Int) := by
    rw [show ((ExpCertV.H129 : Nat) : Int) = 235865763225513294137944142764154484399 from by
      unfold ExpCertV.H129; norm_num]
    linarith [htlo]
  -- denominators (positivity via the global over floor on the nonpositive half)
  have hD : 1108965543718 * 2 ^ 725 ≤ DENv v t := DENv_ge_neg (by omega) htnp
  have hD1 : 1108965543718 * 2 ^ 725 ≤ DENv (v + 1) t := DENv_ge_neg (by omega) htnp
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
  -- part 2: Qw − Qv ≤ Qv1 − Qv = one K-step, |t|-monotone, floored at the piece cap t = −T
  have hQw_le_Qv1 : (evalPoly ExpCertV.numExpV t : Real) / (evalPoly ExpCertV.denExpV t : Real) ≤
      (NUMv (v + 1) t : Real) / (DENv (v + 1) t : Real) := by
    rw [div_le_div_iff₀ hDER hD1R]
    exact_mod_cast htie2
  have hstep_eq : (NUMv (v + 1) t : Real) / (DENv (v + 1) t : Real) -
      (NUMv v t : Real) / (DENv v t : Real) =
      ((2 * (-t) * 2 ^ 111 * KpM v : Int) : Real) /
        ((DENv (v + 1) t : Real) * (DENv v t : Real)) := by
    rw [div_sub_div _ _ (ne_of_gt hD1R) (ne_of_gt hDR)]
    congr 1
    have hid := step_identity v t
    have hswap : NUMv (v + 1) t * DENv v t - DENv (v + 1) t * NUMv v t =
        2 * (-t) * 2 ^ 111 * KpM v := by linear_combination -hid
    rw [show ((2 * (-t) * 2 ^ 111 * KpM v : Int) : Real) =
        ((NUMv (v + 1) t * DENv v t - DENv (v + 1) t * NUMv v t : Int) : Real) from by
      exact_mod_cast (congrArg (fun z : Int => (z : Real)) hswap.symm)]
    push_cast
    ring
  -- the |t|-monotonicity: u·D(T)·D′(T) ≤ T·D(u)·D′(u) with u = −t ≤ T (the piece cap)
  set u : Int := -t with hudef
  have hu0 : (0:Int) ≤ u := by rw [hudef]; linarith [htnp]
  have hntT : u ≤ T := by
    by_contra hgt
    push_neg at hgt
    have hu2 : u ^ 2 = t ^ 2 := by rw [hudef]; ring
    nlinarith [hT2, hu0, hTnn, hgt, hu2]
  set A : Int := (evNumV v : Int) * 2 ^ 111 with hAdef
  set Bo : Int := (odNumV v : Int) with hBodef
  set A1 : Int := (evNumV (v + 1) : Int) * 2 ^ 111 with hA1def
  set Bo1 : Int := (odNumV (v + 1) : Int) with hBo1def
  have hBo_nn : (0:Int) ≤ Bo := Int.natCast_nonneg _
  have hBo1_nn : (0:Int) ≤ Bo1 := Int.natCast_nonneg _
  have hDO725 : (0:Int) < DO * 2 ^ 725 := mul_pos hDOpos (by positivity)
  have hDU725 : (0:Int) < DU * 2 ^ 725 := mul_pos hDUpos (by positivity)
  have hAB : T * Bo ≤ A := by linarith [hflO, hDO725]
  have hA1B1 : T * Bo1 ≤ A1 := by linarith [hflO1, hDO725]
  have hDu : DENv v t = A + u * Bo := by unfold DENv; rw [hAdef, hBodef, hudef]; ring
  have hDu1 : DENv (v + 1) t = A1 + u * Bo1 := by
    unfold DENv; rw [hA1def, hBo1def, hudef]; ring
  have hmono : u * ((A + T * Bo) * (A1 + T * Bo1)) ≤ T * ((A + u * Bo) * (A1 + u * Bo1)) := by
    have hid : T * ((A + u * Bo) * (A1 + u * Bo1)) -
        u * ((A + T * Bo) * (A1 + T * Bo1)) =
        (T - u) * (A * A1 - T * u * (Bo * Bo1)) := by ring
    have hprod : T * u * (Bo * Bo1) ≤ A * A1 := by
      have h1 : T * u * (Bo * Bo1) ≤ T * T * (Bo * Bo1) := by
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hntT hTnn)
          (mul_nonneg hBo_nn hBo1_nn)
        linarith [this]
      have h2 : (T * T * (Bo * Bo1) : Int) = (T * Bo) * (T * Bo1) := by ring
      have h3 : (T * Bo) * (T * Bo1) ≤ A * A1 :=
        mul_le_mul hAB hA1B1
          (mul_nonneg hTnn hBo1_nn)
          (le_trans (mul_nonneg hTnn hBo_nn) hAB)
      linarith [h1, h2 ▸ h1, h3]
    have hfac1 : (0:Int) ≤ T - u := by linarith [hntT]
    have hfac2 : (0:Int) ≤ A * A1 - T * u * (Bo * Bo1) := by
      linarith [hprod]
    linarith only [mul_nonneg hfac1 hfac2, hid]
  -- floor the piece-cap denominators with the under certificate
  have hDH : DU * 2 ^ 725 ≤ A + T * Bo := by linarith [hflU]
  have hDH1 : DU * 2 ^ 725 ≤ A1 + T * Bo1 := by linarith [hflU1]
  have hDHpos : (0:Int) < A + T * Bo := lt_of_lt_of_le hDU725 hDH
  have hDH1pos : (0:Int) < A1 + T * Bo1 := lt_of_lt_of_le hDU725 hDH1
  have hKnn := KpM_nonneg v
  -- the fraction chain: u-step ≤ T-step ≤ piece maximum
  have hfracu : ((2 * u * 2 ^ 111 * KpM v : Int) : Real) /
      ((DENv (v + 1) t : Real) * (DENv v t : Real)) ≤
      ((2 * T * 2 ^ 111 * KpM v : Int) : Real) /
        (((A1 + T * Bo1 : Int) : Real) * ((A + T * Bo : Int) : Real)) := by
    have hdd : (0:Real) < (DENv (v + 1) t : Real) * (DENv v t : Real) := mul_pos hD1R hDR
    have hdH : (0:Real) < ((A1 + T * Bo1 : Int) : Real) * ((A + T * Bo : Int) : Real) := by
      have h1 : (0:Real) < ((A1 + T * Bo1 : Int) : Real) := by exact_mod_cast hDH1pos
      have h2 : (0:Real) < ((A + T * Bo : Int) : Real) := by exact_mod_cast hDHpos
      exact mul_pos h1 h2
    rw [div_le_div_iff₀ hdd hdH]
    -- cross-multiplied: (2u·2^110·Kp)·(D1(T)·D(T)) ≤ (2T·2^110·Kp)·(D1(u)·D(u))
    have hint : (2 * u * 2 ^ 111 * KpM v) * ((A1 + T * Bo1) * (A + T * Bo)) ≤
        (2 * T * 2 ^ 111 * KpM v) * ((A1 + u * Bo1) * (A + u * Bo)) := by
      have hc : (0:Int) ≤ 2 * 2 ^ 111 * KpM v :=
        mul_nonneg (by norm_num) hKnn
      have hscaled := mul_le_mul_of_nonneg_left hmono hc
      linarith only [hscaled]
    have hrw : (DENv (v + 1) t : Real) * (DENv v t : Real) =
        (((A1 + u * Bo1) * (A + u * Bo) : Int) : Real) := by
      rw [hDu, hDu1]; push_cast; ring
    rw [hrw]
    calc ((2 * u * 2 ^ 111 * KpM v : Int) : Real) *
          (((A1 + T * Bo1 : Int) : Real) * ((A + T * Bo : Int) : Real))
        = (((2 * u * 2 ^ 111 * KpM v) *
            ((A1 + T * Bo1) * (A + T * Bo)) : Int) : Real) := by
          push_cast; ring
      _ ≤ (((2 * T * 2 ^ 111 * KpM v) * ((A1 + u * Bo1) * (A + u * Bo)) : Int) : Real) := by
          exact_mod_cast hint
      _ = ((2 * T * 2 ^ 111 * KpM v : Int) : Real) *
            (((A1 + u * Bo1) * (A + u * Bo) : Int) : Real) := by push_cast; ring
  have hfracH : ((2 * T * 2 ^ 111 * KpM v : Int) : Real) /
      (((A1 + T * Bo1 : Int) : Real) * ((A + T * Bo : Int) : Real)) ≤
      ((2 * T * 2 ^ 111 * Khi : Int) : Real) /
        (((DU * 2 ^ 725 : Int) : Real) * ((DU * 2 ^ 725 : Int) : Real)) := by
    have hdH : (0:Real) < ((A1 + T * Bo1 : Int) : Real) * ((A + T * Bo : Int) : Real) := by
      have h1 : (0:Real) < ((A1 + T * Bo1 : Int) : Real) := by exact_mod_cast hDH1pos
      have h2 : (0:Real) < ((A + T * Bo : Int) : Real) := by exact_mod_cast hDHpos
      exact mul_pos h1 h2
    have hDUR : (0:Real) < ((DU * 2 ^ 725 : Int) : Real) := by exact_mod_cast hDU725
    rw [div_le_div_iff₀ hdH (by positivity)]
    have hTc : (0:Int) ≤ 2 * T * 2 ^ 111 :=
      mul_nonneg (mul_nonneg (by norm_num) hTnn) (by norm_num)
    have hnum : ((2 * T * 2 ^ 111 * KpM v : Int) : Real) ≤
        ((2 * T * 2 ^ 111 * Khi : Int) : Real) := by
      have : (2 * T * 2 ^ 111 * KpM v : Int) ≤ 2 * T * 2 ^ 111 * Khi :=
        mul_le_mul_of_nonneg_left hK hTc
      exact_mod_cast this
    have hnum_nn : (0:Real) ≤ ((2 * T * 2 ^ 111 * KpM v : Int) : Real) := by
      have : (0:Int) ≤ 2 * T * 2 ^ 111 * KpM v := mul_nonneg hTc hKnn
      exact_mod_cast this
    have hden : (((DU * 2 ^ 725 : Int) : Real) * ((DU * 2 ^ 725 : Int) : Real)) ≤
        ((A1 + T * Bo1 : Int) : Real) * ((A + T * Bo : Int) : Real) := by
      have h1 : ((DU * 2 ^ 725 : Int) : Real) ≤ ((A1 + T * Bo1 : Int) : Real) := by
        exact_mod_cast hDH1
      have h2 : ((DU * 2 ^ 725 : Int) : Real) ≤ ((A + T * Bo : Int) : Real) := by
        exact_mod_cast hDH
      exact mul_le_mul h1 h2 (le_of_lt hDUR) (by exact_mod_cast le_of_lt hDH1pos)
    calc ((2 * T * 2 ^ 111 * KpM v : Int) : Real) *
          (((DU * 2 ^ 725 : Int) : Real) * ((DU * 2 ^ 725 : Int) : Real))
        ≤ ((2 * T * 2 ^ 111 * Khi : Int) : Real) *
          (((DU * 2 ^ 725 : Int) : Real) * ((DU * 2 ^ 725 : Int) : Real)) :=
          mul_le_mul_of_nonneg_right hnum (by positivity)
      _ ≤ ((2 * T * 2 ^ 111 * Khi : Int) : Real) *
          (((A1 + T * Bo1 : Int) : Real) * ((A + T * Bo : Int) : Real)) := by
          apply mul_le_mul_of_nonneg_left hden
          exact le_trans hnum_nn hnum
  -- the piece budget, Mp-factor included
  have hbudget : (2 ^ 126 : Real) * ((2 ^ 131 : Real) / ((2 ^ 131 : Real) - 1)) *
      (((2 * T * 2 ^ 111 * Khi : Int) : Real) /
        (((DU * 2 ^ 725 : Int) : Real) * ((DU * 2 ^ 725 : Int) : Real))) ≤
      1644901622230542074 / 10000000000000000000 := by
    have hMp1 : (0:Real) < (2 ^ 131 : Real) - 1 := by norm_num
    have hDUR : (0:Real) < ((DU * 2 ^ 725 : Int) : Real) := by exact_mod_cast hDU725
    have hDD : (0:Real) < ((DU * 2 ^ 725 : Int) : Real) * ((DU * 2 ^ 725 : Int) : Real) :=
      mul_pos hDUR hDUR
    rw [show (2 ^ 126 : Real) * ((2 ^ 131 : Real) / ((2 ^ 131 : Real) - 1)) =
        (2 ^ 126 * 2 ^ 131 : Real) / ((2 ^ 131 : Real) - 1) from by rw [mul_div_assoc],
      div_mul_div_comm]
    rw [div_le_div_iff₀ (mul_pos hMp1 hDD) (by norm_num : (0:Real) < 10000000000000000000)]
    have hint : (2 ^ 126 * 2 ^ 131 : Int) * (2 * T * 2 ^ 111 * Khi) * 10000000000000000000 ≤
        (1644901622230542074 : Int) *
          ((2 ^ 131 - 1) * ((DU * 2 ^ 725) * (DU * 2 ^ 725))) := by
      calc (2 ^ 126 * 2 ^ 131 : Int) * (2 * T * 2 ^ 111 * Khi) * 10000000000000000000
          = 2 ^ 126 * 2 ^ 131 * (2 * T * 2 ^ 111 * Khi) * 10000000000000000000 := by ring
        _ ≤ _ := hbudU
    calc (2 ^ 126 * 2 ^ 131 : Real) * ((2 * T * 2 ^ 111 * Khi : Int) : Real) *
          10000000000000000000
        = (((2 ^ 126 * 2 ^ 131 : Int) * (2 * T * 2 ^ 111 * Khi) *
            10000000000000000000 : Int) : Real) := by push_cast; ring
      _ ≤ (((1644901622230542074 : Int) *
            ((2 ^ 131 - 1) * ((DU * 2 ^ 725) * (DU * 2 ^ 725))) : Int) : Real) := by
          exact_mod_cast hint
      _ = (1644901622230542074 : Real) *
            (((2 ^ 131 : Real) - 1) *
              (((DU * 2 ^ 725 : Int) : Real) * ((DU * 2 ^ 725 : Int) : Real))) := by
          push_cast; ring
  -- assemble part 2
  have hgap_le : (evalPoly ExpCertV.numExpV t : Real) / (evalPoly ExpCertV.denExpV t : Real) -
      (NUMv v t : Real) / (DENv v t : Real) ≤
      ((2 * T * 2 ^ 111 * Khi : Int) : Real) /
        (((DU * 2 ^ 725 : Int) : Real) * ((DU * 2 ^ 725 : Int) : Real)) := by
    have hu_eq : ((2 * u * 2 ^ 111 * KpM v : Int) : Real) =
        ((2 * (-t) * 2 ^ 111 * KpM v : Int) : Real) := by rw [hudef]
    calc (evalPoly ExpCertV.numExpV t : Real) / (evalPoly ExpCertV.denExpV t : Real) -
          (NUMv v t : Real) / (DENv v t : Real)
        ≤ (NUMv (v + 1) t : Real) / (DENv (v + 1) t : Real) -
          (NUMv v t : Real) / (DENv v t : Real) := by linarith [hQw_le_Qv1]
      _ = ((2 * (-t) * 2 ^ 111 * KpM v : Int) : Real) /
          ((DENv (v + 1) t : Real) * (DENv v t : Real)) := hstep_eq
      _ = ((2 * u * 2 ^ 111 * KpM v : Int) : Real) /
          ((DENv (v + 1) t : Real) * (DENv v t : Real)) := by rw [hu_eq]
      _ ≤ ((2 * T * 2 ^ 111 * KpM v : Int) : Real) /
          (((A1 + T * Bo1 : Int) : Real) * ((A + T * Bo : Int) : Real)) := hfracu
      _ ≤ ((2 * T * 2 ^ 111 * Khi : Int) : Real) /
          (((DU * 2 ^ 725 : Int) : Real) * ((DU * 2 ^ 725 : Int) : Real)) := hfracH
  have hMpnn : (0:Real) ≤ (2 ^ 126 : Real) * ((2 ^ 131 : Real) / ((2 ^ 131 : Real) - 1)) := by
    have : (0:Real) < (2 ^ 131 : Real) - 1 := by norm_num
    positivity
  exact le_trans (mul_le_mul_of_nonneg_left hgap_le hMpnn) hbudget

end

end ExpYul
