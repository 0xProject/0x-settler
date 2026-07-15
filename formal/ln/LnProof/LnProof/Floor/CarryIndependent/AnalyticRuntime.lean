import Mathlib.Analysis.Calculus.Deriv.MeanValue
import LnProof.Floor.CarryIndependent.Atanh
import LnProof.Floor.CarryIndependent.Normalization

open scoped BigOperators
open Set

namespace LnFloorCarry

open Finset LnYul

set_option maxRecDepth 8192

noncomputable section

private def crossLog (t : Real) : Real :=
  Real.log (1 + t) - Real.log (1 - t)

private def crossTerm (t : Real) (j : Nat) : Real :=
  2 * t * ((t ^ 2) ^ j / (2 * j + 1))

private def derivativeTerm (v : Real) (j : Nat) : Real :=
  (j + 1) * v ^ j / (2 * (j + 1) + 1)

private def derivativeSeries (v : Real) : Real :=
  ∑' j : Nat, derivativeTerm v j

theorem atanhSeries_summable {v : Real} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    Summable (fun j : Nat => v ^ j / (2 * j + 1)) := by
  have hgeom := summable_geometric_of_lt_one hv0 hv1
  apply hgeom.of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (pow_nonneg hv0 _) (by positivity))]
  have hj0 : (0 : Real) ≤ j := Nat.cast_nonneg j
  exact div_le_self (pow_nonneg hv0 _) (by nlinarith)

theorem atanhSeries_nonneg {v : Real} (hv0 : 0 ≤ v) :
    0 ≤ atanhSeries v := by
  unfold atanhSeries
  apply tsum_nonneg
  intro j
  exact div_nonneg (pow_nonneg hv0 _) (by positivity)

theorem atanhSeries_mono {v w : Real}
    (hv0 : 0 ≤ v) (hvw : v ≤ w) (hw1 : w < 1) :
    atanhSeries v ≤ atanhSeries w := by
  have hw0 : 0 ≤ w := hv0.trans hvw
  have hv1 : v < 1 := hvw.trans_lt hw1
  unfold atanhSeries
  apply (atanhSeries_summable hv0 hv1).tsum_le_tsum _
    (atanhSeries_summable hw0 hw1)
  intro j
  exact div_le_div_of_nonneg_right ((pow_le_pow_left₀ hv0 hvw j)) (by positivity)

theorem crossLog_eq_atanhSeries {t : Real} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    crossLog t = 2 * t * atanhSeries (t ^ 2) := by
  have htAbs : |t| < 1 := by simpa [abs_of_nonneg ht0] using ht1
  have hlog : HasSum (crossTerm t) (crossLog t) := by
    convert Real.hasSum_log_sub_log_of_abs_lt_one htAbs using 1
    ext j
    simp only [crossTerm]
    ring
  rw [← hlog.tsum_eq]
  unfold atanhSeries
  simpa only [crossTerm] using
    (tsum_mul_left (a := 2 * t)
      (f := fun j : Nat => (t ^ 2) ^ j / (2 * j + 1)))

theorem crossLog_hasDerivAt {t : Real} (htm : -1 < t) (htp : t < 1) :
    HasDerivAt crossLog (2 / (1 - t ^ 2)) t := by
  have hp0 : (1 : Real) + t ≠ 0 := by nlinarith
  have hm0 : (1 : Real) - t ≠ 0 := by nlinarith
  have hp := (Real.hasDerivAt_log hp0).comp t
    ((hasDerivAt_const t 1).add (hasDerivAt_id t))
  have hm := (Real.hasDerivAt_log hm0).comp t
    ((hasDerivAt_const t 1).sub (hasDerivAt_id t))
  have hsq : 1 - t ^ 2 ≠ 0 := by nlinarith [sq_nonneg t]
  unfold crossLog
  convert hp.sub hm using 1; field_simp [hp0, hm0, hsq]; ring_nf

theorem crossLog_increment_le {a t T : Real}
    (ha0 : 0 ≤ a) (hat : a ≤ t) (htT : t ≤ T)
    (hT0 : 0 < T) (hT1 : T < 1) :
    crossLog t - crossLog a ≤ (2 / (1 - T ^ 2)) * (t - a) := by
  have hdiffOn : DifferentiableOn Real crossLog (Icc 0 T) := by
    intro x hx
    have hxm : -1 < x := by nlinarith [hx.1]
    have hxp : x < 1 := by nlinarith [hx.2]
    exact (crossLog_hasDerivAt hxm hxp).differentiableAt.differentiableWithinAt
  apply (convex_Icc (0 : Real) T).image_sub_le_mul_sub_of_deriv_le
    hdiffOn.continuousOn (hdiffOn.mono interior_subset)
  · intro x hx
    have hxI : x ∈ Icc (0 : Real) T := interior_subset hx
    have hxm : -1 < x := by nlinarith [hxI.1]
    have hxp : x < 1 := by nlinarith [hxI.2]
    rw [(crossLog_hasDerivAt hxm hxp).deriv]
    have hdx : 0 < 1 - x ^ 2 := by nlinarith [sq_nonneg x]
    have hdT : 0 < 1 - T ^ 2 := by nlinarith [sq_nonneg T]
    rw [div_le_div_iff₀ hdx hdT]
    have hsq := (sq_le_sq₀ hxI.1 hT0.le).2 hxI.2
    nlinarith
  · exact ⟨ha0, hat.trans htT⟩
  · exact ⟨ha0.trans hat, htT⟩
  · exact hat

theorem pow_sub_pow_le_endpoint {v w V : Real}
    (hv0 : 0 ≤ v) (hvw : v ≤ w) (hwV : w ≤ V) (n : Nat) :
    w ^ (n + 1) - v ^ (n + 1) ≤
      (n + 1) * V ^ n * (w - v) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hw0 : 0 ≤ w := hv0.trans hvw
      have hV0 : 0 ≤ V := hw0.trans hwV
      have hstep :
          w ^ (n + 2) - v ^ (n + 2) =
            w * (w ^ (n + 1) - v ^ (n + 1)) + v ^ (n + 1) * (w - v) := by
        ring
      rw [hstep]
      have h1 := mul_le_mul_of_nonneg_left ih hw0
      have hwPow : w * V ^ n ≤ V ^ (n + 1) := by
        simpa only [pow_succ, mul_comm] using
          mul_le_mul_of_nonneg_right hwV (pow_nonneg hV0 n)
      have hvPow : v ^ (n + 1) ≤ V ^ (n + 1) := by
        exact pow_le_pow_left₀ hv0 (hvw.trans hwV) _
      have hdelta : 0 ≤ w - v := sub_nonneg.mpr hvw
      have hcoef0 : (0 : Real) ≤ (n : Real) + 1 := by
        exact add_nonneg (Nat.cast_nonneg n) zero_le_one
      have hfirst :
          w * (((n : Real) + 1) * V ^ n * (w - v)) ≤
            ((n : Real) + 1) * V ^ (n + 1) * (w - v) := by
        calc
          w * (((n : Real) + 1) * V ^ n * (w - v)) =
              ((n : Real) + 1) * (w * V ^ n) * (w - v) := by ring
          _ ≤ ((n : Real) + 1) * V ^ (n + 1) * (w - v) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hwPow hcoef0) hdelta
      have hsecond :
          v ^ (n + 1) * (w - v) ≤ V ^ (n + 1) * (w - v) :=
        mul_le_mul_of_nonneg_right hvPow hdelta
      have hsuccCast : (n : Real) + 2 = (((n + 1 : Nat) : Real) + 1) := by
        rw [Nat.cast_add, Nat.cast_one]
        ring
      calc
        w * (w ^ (n + 1) - v ^ (n + 1)) + v ^ (n + 1) * (w - v) ≤
            w * (((n : Real) + 1) * V ^ n * (w - v)) +
              v ^ (n + 1) * (w - v) := add_le_add_right h1 _
        _ ≤ ((n : Real) + 1) * V ^ (n + 1) * (w - v) +
              V ^ (n + 1) * (w - v) := add_le_add hfirst hsecond
        _ = ((n : Real) + 2) * V ^ (n + 1) * (w - v) := by ring
        _ = (((n + 1 : Nat) : Real) + 1) * V ^ (n + 1) * (w - v) :=
          congrArg (fun c : Real => c * V ^ (n + 1) * (w - v)) hsuccCast

theorem derivativeSeries_summable {v : Real} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    Summable (derivativeTerm v) := by
  have habs : ‖v‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hv0] using hv1
  have hweighted : Summable (fun j : Nat => (j + 1 : Real) * v ^ j) := by
    have hlinear := summable_pow_mul_geometric_of_norm_lt_one 1 habs
    have hgeom := summable_geometric_of_lt_one hv0 hv1
    convert hlinear.add hgeom using 1
    ext j
    norm_num
    ring
  apply hweighted.of_norm_bounded
  intro j
  have hj0 : (0 : Real) ≤ j := Nat.cast_nonneg j
  have hcoef0 : (0 : Real) ≤ (j : Real) + 1 := add_nonneg hj0 zero_le_one
  have hnum0 : 0 ≤ ((j : Real) + 1) * v ^ j :=
    mul_nonneg hcoef0 (pow_nonneg hv0 j)
  have hden0 : 0 ≤ 2 * ((j : Real) + 1) + 1 := by nlinarith
  unfold derivativeTerm
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum0 hden0)]
  exact div_le_self hnum0 (by nlinarith)

theorem atanhSeries_increment_le {v w V : Real}
    (hv0 : 0 ≤ v) (hvw : v ≤ w) (hwV : w ≤ V) (hV1 : V < 1) :
    atanhSeries w - atanhSeries v ≤ (w - v) * derivativeSeries V := by
  have hw0 : 0 ≤ w := hv0.trans hvw
  have hV0 : 0 ≤ V := hw0.trans hwV
  have hw1 : w < 1 := hwV.trans_lt hV1
  have hv1 : v < 1 := hvw.trans_lt hw1
  have hsw := atanhSeries_summable hw0 hw1
  have hsv := atanhSeries_summable hv0 hv1
  have hdiff := hsw.sub hsv
  have hderiv := derivativeSeries_summable hV0 hV1
  have htail : Summable (fun j : Nat =>
      (w ^ (j + 1) - v ^ (j + 1)) / (2 * (j + 1) + 1)) := by
    have hs := (summable_nat_add_iff 1).2 hdiff
    convert hs using 1
    ext j
    push_cast
    ring
  have htailLe :
      (∑' j : Nat,
          (w ^ (j + 1) - v ^ (j + 1)) / (2 * (j + 1) + 1)) ≤
        ∑' j : Nat, (w - v) * derivativeTerm V j := by
    apply htail.tsum_le_tsum _ (hderiv.mul_left (w - v))
    intro j
    unfold derivativeTerm
    have hpow := pow_sub_pow_le_endpoint hv0 hvw hwV j
    have hj0 : (0 : Real) ≤ j := Nat.cast_nonneg j
    have hden : (0 : Real) ≤ 2 * ((j : Real) + 1) + 1 := by nlinarith
    calc
      (w ^ (j + 1) - v ^ (j + 1)) / (2 * (j + 1) + 1) ≤
          (((j : Real) + 1) * V ^ j * (w - v)) / (2 * (j + 1) + 1) :=
        div_le_div_of_nonneg_right hpow hden
      _ = (w - v) * ((j + 1) * V ^ j / (2 * (j + 1) + 1)) := by ring
  have hshiftEq :
      (∑' j : Nat,
          (w ^ (j + 1) / (2 * (j + 1) + 1) -
            v ^ (j + 1) / (2 * (j + 1) + 1))) =
        ∑' j : Nat,
          (w ^ (j + 1) - v ^ (j + 1)) / (2 * (j + 1) + 1) := by
    apply tsum_congr
    intro j
    ring
  unfold atanhSeries derivativeSeries
  rw [← hsw.tsum_sub hsv, ← hdiff.sum_add_tsum_nat_add 1]
  simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, sub_self]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [hshiftEq, ← tsum_mul_left]
  exact htailLe

theorem derivativeSeries_endpoint_le :
    derivativeSeries endpointV ≤ endpointDerivative := by
  have hV0 : 0 ≤ endpointV := by unfold endpointV; positivity
  have hV1 : endpointV < 1 := by
    norm_num [endpointV, endpointZ, endpointZWord, wordQ100]
  have hs := derivativeSeries_summable hV0 hV1
  have htail := (summable_nat_add_iff 48).2 hs
  have hgeom : Summable (fun j : Nat =>
      endpointV ^ 48 / 2 * endpointV ^ j) :=
    (summable_geometric_of_lt_one hV0 hV1).mul_left (endpointV ^ 48 / 2)
  have htailLe :
      (∑' j : Nat, derivativeTerm endpointV (j + 48)) ≤
        ∑' j : Nat, endpointV ^ 48 / 2 * endpointV ^ j := by
    apply htail.tsum_le_tsum _ hgeom
    intro j
    unfold derivativeTerm
    have hj0 : (0 : Real) ≤ j := Nat.cast_nonneg j
    have hcoef : ((j : Real) + 49) / (2 * ((j : Real) + 49) + 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    rw [pow_add]
    push_cast
    calc
      ((j : Real) + 48 + 1) * (endpointV ^ j * endpointV ^ 48) /
          (2 * ((j : Real) + 48 + 1) + 1) =
          (((j : Real) + 49) / (2 * ((j : Real) + 49) + 1)) *
            (endpointV ^ 48 * endpointV ^ j) := by ring
      _ ≤ (1 / 2) * (endpointV ^ 48 * endpointV ^ j) :=
        mul_le_mul_of_nonneg_right hcoef (mul_nonneg (pow_nonneg hV0 _) (pow_nonneg hV0 _))
      _ = endpointV ^ 48 / 2 * endpointV ^ j := by ring
  unfold derivativeSeries endpointDerivative
  rw [← hs.sum_add_tsum_nat_add 48]
  calc
    (∑ j ∈ range 48, derivativeTerm endpointV j) +
          ∑' j : Nat, derivativeTerm endpointV (j + 48) ≤
        (∑ j ∈ range 48, derivativeTerm endpointV j) +
          ∑' j : Nat, endpointV ^ 48 / 2 * endpointV ^ j :=
      add_le_add_left htailLe _
    _ = (∑ j ∈ range 48,
          (j + 1) * endpointV ^ j / (2 * (j + 1) + 1)) +
        endpointV ^ 48 / (2 * (1 - endpointV)) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hV0 hV1]
      simp only [derivativeTerm]
      field_simp [show (1 : Real) - endpointV ≠ 0 by linarith]

theorem endpointDerivative_nonneg : 0 ≤ endpointDerivative := by
  have hV0 : 0 ≤ endpointV := by unfold endpointV; positivity
  have hseries0 : 0 ≤ derivativeSeries endpointV := by
    unfold derivativeSeries derivativeTerm
    apply tsum_nonneg
    intro j
    exact div_nonneg
      (mul_nonneg (add_nonneg (Nat.cast_nonneg j) zero_le_one) (pow_nonneg hV0 j))
      (by positivity)
  exact hseries0.trans derivativeSeries_endpoint_le

theorem low_log_error_lt_components {m : Nat}
    (hmlo : 2 ^ 95 ≤ m) (hmsc : m < Sc) :
    rayScale * (lowShadow m - Real.log ((m : Real) / Sc)) <
      approximationTerm m + hornerTerm m + zFloorBudget + uFloorBudget +
        closingDivisionBudget := by
  let t := ((Sc : Real) - m) / ((Sc : Real) + m)
  let a := normalizedZ m
  let v := normalizedU m
  have hm : 0 < m := (by norm_num : 0 < 2 ^ 95).trans_le hmlo
  have hma := low_z_floor hmlo hmsc
  have huv := low_u_floor hmlo hmsc
  obtain ⟨ha0, haEnd, htEnd, hEnd1⟩ := low_endpoint_bounds hmlo hmsc
  have hEnd0 : 0 < endpointT := by norm_num [endpointT, Sc]
  have ht0 : 0 ≤ t := by
    dsimp [t]
    have hmSc : (m : Real) ≤ Sc := by exact_mod_cast Nat.le_of_lt hmsc
    exact div_nonneg (sub_nonneg.mpr hmSc)
      (add_nonneg (Nat.cast_nonneg Sc) (Nat.cast_nonneg m))
  have ha1 : a < 1 := haEnd.trans_lt (by
    norm_num [endpointZ, endpointZWord, wordQ100])
  have hcrossZ := crossLog_increment_le ha0 hma.1 htEnd hEnd0 hEnd1
  have hmaUpper : t < a + 1 / wordQ100 := by
    simpa only [t, a] using hma.2
  have hdeltaZ : t - a < 1 / wordQ100 := by
    apply sub_lt_iff_lt_add.mpr
    simpa only [add_comm] using hmaUpper
  have hcoefZ : 0 < 2 / (1 - endpointT ^ 2) := by
    have hsq : endpointT ^ 2 < 1 := by nlinarith [sq_nonneg endpointT]
    exact div_pos (by norm_num) (sub_pos.mpr hsq)
  have hcrossZStrict :
      crossLog t < crossLog a + 2 / wordQ100 / (1 - endpointT ^ 2) := by
    have hscaled := mul_lt_mul_of_pos_left hdeltaZ hcoefZ
    have hcrossZ' : crossLog t - crossLog a ≤
        (2 / (1 - endpointT ^ 2)) * (t - a) := by
      simpa only [t, a] using hcrossZ
    have hcrossLe := sub_le_iff_le_add.mp hcrossZ'
    calc
      crossLog t ≤ crossLog a + (2 / (1 - endpointT ^ 2)) * (t - a) :=
        (by simpa only [add_comm] using hcrossLe)
      _ < crossLog a + (2 / (1 - endpointT ^ 2)) * (1 / wordQ100) :=
        add_lt_add_left hscaled _
      _ = crossLog a + 2 / wordQ100 / (1 - endpointT ^ 2) := by ring
  have hV0 : 0 ≤ endpointV := by
    unfold endpointV
    exact sq_nonneg endpointZ
  have hV1 : endpointV < 1 := by
    norm_num [endpointV, endpointZ, endpointZWord, wordQ100]
  have haSqEnd : a ^ 2 ≤ endpointV := by
    unfold endpointV
    have hEndpointZ0 : 0 ≤ endpointZ := by
      unfold endpointZ
      exact div_nonneg (Nat.cast_nonneg endpointZWord) (Nat.cast_nonneg wordQ100)
    exact (sq_le_sq₀ ha0 hEndpointZ0).2 haEnd
  have hv0 : 0 ≤ v := by
    dsimp [v]
    unfold normalizedU
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg wordQ96)
  have hseries := atanhSeries_increment_le hv0 huv.1 haSqEnd hV1
  have hseriesEnd := derivativeSeries_endpoint_le
  have huvUpper : a ^ 2 < v + 1 / wordQ96 := by
    simpa only [a, v] using huv.2
  have hdeltaU : a ^ 2 - v < 1 / wordQ96 := by
    apply sub_lt_iff_lt_add.mpr
    simpa only [add_comm] using huvUpper
  have hseriesLe :
      atanhSeries (a ^ 2) ≤ atanhSeries v + endpointDerivative / wordQ96 := by
    have hscaled : (a ^ 2 - v) * derivativeSeries endpointV ≤
        (1 / wordQ96) * endpointDerivative := by
      calc
        (a ^ 2 - v) * derivativeSeries endpointV ≤
            (a ^ 2 - v) * endpointDerivative :=
          mul_le_mul_of_nonneg_left hseriesEnd (sub_nonneg.mpr huv.1)
        _ ≤ (1 / wordQ96) * endpointDerivative :=
          mul_le_mul_of_nonneg_right hdeltaU.le endpointDerivative_nonneg
    calc
      atanhSeries (a ^ 2) ≤
          atanhSeries v + (a ^ 2 - v) * derivativeSeries endpointV :=
        (by
          have hseries' : atanhSeries (a ^ 2) - atanhSeries v ≤
              (a ^ 2 - v) * derivativeSeries endpointV := by
            simpa only [a] using hseries
          have hseriesAdd := sub_le_iff_le_add.mp hseries'
          simpa only [add_comm] using hseriesAdd)
      _ ≤ atanhSeries v + (1 / wordQ96) * endpointDerivative :=
        add_le_add_left hscaled _
      _ = atanhSeries v + endpointDerivative / wordQ96 := by ring
  have hcrossA := crossLog_eq_atanhSeries ha0 ha1
  have hlogCross : -Real.log ((m : Real) / (Sc : Real)) = crossLog t := by
    simpa [t, crossLog] using neg_log_ratio_eq_log_sub_log
      (m := (m : Real)) (S := (Sc : Real)) (by exact_mod_cast hm)
      (by exact_mod_cast Nat.le_of_lt hmsc)
  have hlog :
      -Real.log ((m : Real) / (Sc : Real)) <
        2 * a * atanhSeries v +
          2 / wordQ100 / (1 - endpointT ^ 2) +
          2 * a * endpointDerivative / wordQ96 := by
    rw [hlogCross]
    calc
      crossLog t < crossLog a + 2 / wordQ100 / (1 - endpointT ^ 2) :=
        hcrossZStrict
      _ = 2 * a * atanhSeries (a ^ 2) +
          2 / wordQ100 / (1 - endpointT ^ 2) := by rw [hcrossA]
      _ ≤ 2 * a * atanhSeries v +
          2 / wordQ100 / (1 - endpointT ^ 2) +
          2 * a * endpointDerivative / wordQ96 := by
        have hfactor0 : (0 : Real) ≤ 2 * a := mul_nonneg (by norm_num) ha0
        have hmulSeries := mul_le_mul_of_nonneg_left hseriesLe hfactor0
        calc
          2 * a * atanhSeries (a ^ 2) + 2 / wordQ100 / (1 - endpointT ^ 2) ≤
              2 * a * (atanhSeries v + endpointDerivative / wordQ96) +
                2 / wordQ100 / (1 - endpointT ^ 2) :=
            add_le_add_right hmulSeries _
          _ = 2 * a * atanhSeries v + 2 / wordQ100 / (1 - endpointT ^ 2) +
              2 * a * endpointDerivative / wordQ96 := by ring
  have huBudget :
      2 * rayScale * a * endpointDerivative / wordQ96 ≤ uFloorBudget := by
    unfold uFloorBudget
    have hnonneg : 0 ≤ 2 * rayScale * endpointDerivative / wordQ96 :=
      div_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (Nat.cast_nonneg rayScale))
          endpointDerivative_nonneg)
        (Nat.cast_nonneg wordQ96)
    calc
      2 * rayScale * a * endpointDerivative / wordQ96 =
          a * (2 * rayScale * endpointDerivative / wordQ96) := by ring
      _ ≤ endpointZ * (2 * rayScale * endpointDerivative / wordQ96) :=
        mul_le_mul_of_nonneg_right haEnd hnonneg
      _ = 2 * rayScale * endpointZ * endpointDerivative / wordQ96 := by ring
  unfold lowShadow approximationTerm hornerTerm zFloorBudget closingDivisionBudget
  dsimp [a, v] at hlog huBudget ⊢
  have hray : (0 : Real) < rayScale := by norm_num [rayScale]
  have hscaledLog := mul_lt_mul_of_pos_left hlog hray
  have hshiftedLog := add_lt_add_right hscaledLog
    (-2 * rayScale * normalizedZ m * shadowRatio (uWord (zWord m)) +
      2 * rayScale / wordQ100)
  calc
    (rayScale : Real) *
        (-2 * normalizedZ m * shadowRatio (uWord (zWord m)) + 2 / wordQ100 -
          Real.log ((m : Real) / (Sc : Real))) <
      2 * rayScale * normalizedZ m *
          (atanhSeries (normalizedU m) - exactRatio (uWord (zWord m))) +
        2 * rayScale * normalizedZ m *
          (exactRatio (uWord (zWord m)) - shadowRatio (uWord (zWord m))) +
        (2 * rayScale / wordQ100) / (1 - endpointT ^ 2) +
        2 * rayScale * normalizedZ m * endpointDerivative / wordQ96 +
        2 * rayScale / wordQ100 := by
      calc
        (rayScale : Real) *
            (-2 * normalizedZ m * shadowRatio (uWord (zWord m)) + 2 / wordQ100 -
              Real.log ((m : Real) / (Sc : Real))) =
            (rayScale : Real) * (-Real.log ((m : Real) / (Sc : Real))) +
              (-2 * rayScale * normalizedZ m * shadowRatio (uWord (zWord m)) +
                2 * rayScale / wordQ100) := by ring
        _ < (rayScale : Real) *
              (2 * normalizedZ m * atanhSeries (normalizedU m) +
                2 / wordQ100 / (1 - endpointT ^ 2) +
                2 * normalizedZ m * endpointDerivative / wordQ96) +
              (-2 * rayScale * normalizedZ m * shadowRatio (uWord (zWord m)) +
                2 * rayScale / wordQ100) := hshiftedLog
        _ = 2 * rayScale * normalizedZ m *
              (atanhSeries (normalizedU m) - exactRatio (uWord (zWord m))) +
            2 * rayScale * normalizedZ m *
              (exactRatio (uWord (zWord m)) - shadowRatio (uWord (zWord m))) +
            (2 * rayScale / wordQ100) / (1 - endpointT ^ 2) +
            2 * rayScale * normalizedZ m * endpointDerivative / wordQ96 +
            2 * rayScale / wordQ100 := by ring
    _ ≤ 2 * rayScale * normalizedZ m *
          (atanhSeries (normalizedU m) - exactRatio (uWord (zWord m))) +
        2 * rayScale * normalizedZ m *
          (exactRatio (uWord (zWord m)) - shadowRatio (uWord (zWord m))) +
        (2 * rayScale / wordQ100) / (1 - endpointT ^ 2) +
        uFloorBudget + 2 * rayScale / wordQ100 := by
      let common :=
        2 * rayScale * normalizedZ m *
            (atanhSeries (normalizedU m) - exactRatio (uWord (zWord m))) +
          2 * rayScale * normalizedZ m *
            (exactRatio (uWord (zWord m)) - shadowRatio (uWord (zWord m))) +
          (2 * rayScale / wordQ100) / (1 - endpointT ^ 2) +
          2 * rayScale / wordQ100
      calc
        2 * rayScale * normalizedZ m *
              (atanhSeries (normalizedU m) - exactRatio (uWord (zWord m))) +
            2 * rayScale * normalizedZ m *
              (exactRatio (uWord (zWord m)) - shadowRatio (uWord (zWord m))) +
            (2 * rayScale / wordQ100) / (1 - endpointT ^ 2) +
            2 * rayScale * normalizedZ m * endpointDerivative / wordQ96 +
            2 * rayScale / wordQ100 =
            common + 2 * rayScale * normalizedZ m * endpointDerivative / wordQ96 := by
          dsimp [common]
          ring
        _ ≤ common + uFloorBudget := add_le_add_left huBudget common
        _ = 2 * rayScale * normalizedZ m *
              (atanhSeries (normalizedU m) - exactRatio (uWord (zWord m))) +
            2 * rayScale * normalizedZ m *
              (exactRatio (uWord (zWord m)) - shadowRatio (uWord (zWord m))) +
            (2 * rayScale / wordQ100) / (1 - endpointT ^ 2) +
            uFloorBudget + 2 * rayScale / wordQ100 := by
          dsimp [common]
          ring

theorem lowShadow_core_bound {m : Nat}
    (hmlo : 2 ^ 95 ≤ m) (hmsc : m < Sc)
    (hApprox : approximationTerm m ≤ approximationBudget)
    (hHorner : hornerTerm m ≤ hornerBudget) :
    rayScale * (lowShadow m - Real.log ((m : Real) / Sc)) < coreErrorLimit := by
  have hparts := low_log_error_lt_components hmlo hmsc
  calc
    rayScale * (lowShadow m - Real.log ((m : Real) / Sc)) <
        approximationTerm m + hornerTerm m + zFloorBudget + uFloorBudget +
          closingDivisionBudget := hparts
    _ ≤ approximationBudget + hornerBudget + zFloorBudget + uFloorBudget +
          closingDivisionBudget := by linarith
    _ < coreErrorLimit := by
      have htotal := totalBudget_lt_coreErrorLimit
      linarith

theorem high_log_error_le_approximationTerm {m : Nat}
    (hscm : Sc ≤ m) (hmhi : m < 2 ^ 96) :
    rayScale * (highShadow m - Real.log ((m : Real) / Sc)) ≤
      highApproximationTerm m := by
  let t := ((m : Real) - Sc) / ((m : Real) + Sc)
  let b := highNormalizedZ m
  let v := normalizedU m
  obtain ⟨hb0, hbt, ht1⟩ := high_endpoint_bounds hscm hmhi
  have huv := high_u_floor hscm hmhi
  have ht0 : 0 ≤ t := by
    dsimp [t]
    have hscmR : (Sc : Real) ≤ m := by exact_mod_cast hscm
    exact div_nonneg (sub_nonneg.mpr hscmR)
      (add_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg Sc))
  have hbtSq : b ^ 2 ≤ t ^ 2 := (sq_le_sq₀ hb0 ht0).2 hbt
  have htSq1 : t ^ 2 < 1 := by nlinarith [sq_nonneg t]
  have hv0 : 0 ≤ v := by
    dsimp [v]
    unfold normalizedU
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg wordQ96)
  have hseries : atanhSeries v ≤ atanhSeries (t ^ 2) :=
    atanhSeries_mono hv0 (huv.1.trans hbtSq) htSq1
  have hseries0 : 0 ≤ atanhSeries v := atanhSeries_nonneg hv0
  have hmul : b * atanhSeries v ≤ t * atanhSeries (t ^ 2) :=
    mul_le_mul hbt hseries hseries0 ht0
  have hSc : (0 : Real) < Sc := by norm_num [Sc]
  have hscmR : (Sc : Real) ≤ m := by exact_mod_cast hscm
  have hlogCross : Real.log ((m : Real) / (Sc : Real)) = crossLog t := by
    simpa [t, crossLog] using log_ratio_eq_log_sub_log
      (m := (m : Real)) (S := (Sc : Real)) hSc hscmR
  have hcrossT := crossLog_eq_atanhSeries ht0 ht1
  have hlog : 2 * b * atanhSeries v ≤ Real.log ((m : Real) / (Sc : Real)) := by
    rw [hlogCross, hcrossT]
    have htwice := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : Real) ≤ 2)
    simpa only [mul_assoc] using htwice
  have hbase :
      2 * b * exactRatio (uWord (zWord m)) - Real.log ((m : Real) / (Sc : Real)) ≤
        2 * b * (exactRatio (uWord (zWord m)) - atanhSeries v) := by
    calc
      2 * b * exactRatio (uWord (zWord m)) - Real.log ((m : Real) / (Sc : Real)) ≤
          2 * b * exactRatio (uWord (zWord m)) - 2 * b * atanhSeries v :=
        sub_le_sub_left hlog _
      _ = 2 * b * (exactRatio (uWord (zWord m)) - atanhSeries v) := by ring
  have hscaled := mul_le_mul_of_nonneg_left hbase
    (Nat.cast_nonneg rayScale)
  simpa [highShadow, highApproximationTerm, b, v, mul_assoc, mul_comm, mul_left_comm]
    using hscaled

theorem highShadow_core_bound {m : Nat}
    (hscm : Sc ≤ m) (hmhi : m < 2 ^ 96)
    (hApprox : highApproximationTerm m ≤ approximationBudget) :
    rayScale * (highShadow m - Real.log ((m : Real) / Sc)) < coreErrorLimit := by
  have herror := high_log_error_le_approximationTerm hscm hmhi
  exact herror.trans_lt (hApprox.trans_lt approximationBudget_lt_coreErrorLimit)

end

end LnFloorCarry
