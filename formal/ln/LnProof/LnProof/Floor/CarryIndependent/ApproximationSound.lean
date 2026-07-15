import Mathlib.Data.Real.Basic
import LnProof.Floor.CarryIndependent.Approximation

namespace LnFloorCarry

open Common.Poly

set_option maxRecDepth 100000

noncomputable section

private theorem approximationEnvelopeSquareBudget_factor :
    (2 * 10 ^ 27 * approximationErrorDen) ^ 2 *
        approximationEnvelopeSquareBudget =
      (approximationErrorNum * approximationEnvelopeDen) ^ 2 *
        approximationScale := by
  norm_num [approximationErrorNum, approximationErrorDen,
    approximationEnvelopeDen, approximationEnvelopeSquareBudget,
    approximationScale]

theorem approximationEnvelope_scale_nat {hi u z a : Nat}
    (ha : approximationEnvelopeCandidate hi a) (hu : u ≤ hi)
    (hz : z ^ 2 < (u + 1) * 2 ^ 104) :
    (2 * 10 ^ 27 * approximationErrorDen) * a * z ≤
      (approximationErrorNum * approximationEnvelopeDen) * 2 ^ 100 := by
  let C := 2 * 10 ^ 27 * approximationErrorDen
  let P := approximationErrorNum * approximationEnvelopeDen
  have hscaled : a ^ 2 * (C ^ 2 * (hi + 1)) ≤
      P ^ 2 * approximationScale := by
    calc
      a ^ 2 * (C ^ 2 * (hi + 1)) =
          C ^ 2 * (a ^ 2 * (hi + 1)) := by ring
      _ ≤ C ^ 2 * approximationEnvelopeSquareBudget :=
        Nat.mul_le_mul_left _ ha
      _ = P ^ 2 * approximationScale := by
        simpa [C, P] using approximationEnvelopeSquareBudget_factor
  have hzhi : z ^ 2 ≤ (hi + 1) * 2 ^ 104 :=
    (Nat.le_of_lt hz).trans
      (Nat.mul_le_mul_right (2 ^ 104) (Nat.add_le_add_right hu 1))
  have h1 := Nat.mul_le_mul_left (a ^ 2 * C ^ 2) hzhi
  have h2 := Nat.mul_le_mul_right (2 ^ 104) hscaled
  have hsq : (C * a * z) ^ 2 ≤ (P * 2 ^ 100) ^ 2 := calc
    (C * a * z) ^ 2 = a ^ 2 * C ^ 2 * z ^ 2 := by ring
    _ ≤ a ^ 2 * C ^ 2 * ((hi + 1) * 2 ^ 104) := h1
    _ = (a ^ 2 * (C ^ 2 * (hi + 1))) * 2 ^ 104 := by ring
    _ ≤ (P ^ 2 * approximationScale) * 2 ^ 104 := h2
    _ = (P * 2 ^ 100) ^ 2 := by simp [approximationScale]; ring
  have hbase : C * a * z ≤ P * 2 ^ 100 :=
    (Nat.pow_le_pow_iff_left (by decide : (2 : Nat) ≠ 0)).1 hsq
  simpa [C, P]

theorem approximationEnvelope_scale_real {hi u z a : Nat}
    (ha : approximationEnvelopeCandidate hi a) (hu : u ≤ hi)
    (hz : z ^ 2 < (u + 1) * 2 ^ 104) :
    2 * (10 ^ 27 : Real) * ((z : Real) / 2 ^ 100) *
        ((a : Real) / approximationEnvelopeDen) ≤
      (approximationErrorNum : Real) / approximationErrorDen := by
  let C := 2 * 10 ^ 27 * approximationErrorDen
  let P := approximationErrorNum * approximationEnvelopeDen
  have hbase := approximationEnvelope_scale_nat ha hu hz
  have hbaseR : ((C * a * z : Nat) : Real) ≤ ((P * 2 ^ 100 : Nat) : Real) := by
    dsimp [C, P]
    exact_mod_cast hbase
  let den : Real := approximationErrorDen * 2 ^ 100 * approximationEnvelopeDen
  have herrorDen : (0 : Real) < approximationErrorDen := by
    exact_mod_cast (show 0 < approximationErrorDen by
      unfold approximationErrorDen
      positivity)
  have henvelopeDen : (0 : Real) < approximationEnvelopeDen := by
    exact_mod_cast (show 0 < approximationEnvelopeDen by
      unfold approximationEnvelopeDen
      positivity)
  have hden : 0 < den := by
    dsimp [den]
    positivity
  calc
    2 * (10 ^ 27 : Real) * ((z : Real) / 2 ^ 100) *
          ((a : Real) / approximationEnvelopeDen) =
        ((C * a * z : Nat) : Real) / den := by
      dsimp [C, den]
      push_cast
      field_simp [henvelopeDen.ne']
      ring
    _ ≤ ((P * 2 ^ 100 : Nat) : Real) / den :=
      (div_le_div_iff_of_pos_right hden).2 hbaseR
    _ = (approximationErrorNum : Real) / approximationErrorDen := by
      dsimp [P, den]
      push_cast
      field_simp [herrorDen.ne']
      ring

theorem ratio_gap_le_of_cross {a e fn fd n d : Real}
    (he : 0 < e) (hfd : 0 < fd) (hd : 0 < d)
    (h : e * (fn * d - n * fd) ≤ a * (fd * d)) :
    fn / fd - n / d ≤ a / e := by
  rw [le_div_iff₀ he]
  calc
    (fn / fd - n / d) * e = e * (fn * d - n * fd) / (fd * d) := by
      field_simp [hfd.ne', hd.ne']
      ring
    _ ≤ a := (div_le_iff₀ (mul_pos hfd hd)).2 (by
      simpa [mul_assoc] using h)

theorem approximationLowCert_implies_real {a : Nat} {u : Int}
    (hF : 0 < evalPoly approximationUpperDen u)
    (hD : 0 < evalPoly approximationRationalDen u)
    (hcert : 0 ≤ evalPoly (approximationLowCert a) u) :
    (evalPoly approximationUpperNum u : Real) /
          evalPoly approximationUpperDen u -
        (evalPoly approximationRationalNum u : Real) /
          evalPoly approximationRationalDen u ≤
      (a : Real) / approximationEnvelopeDen := by
  have hc : (0 : Real) ≤ evalPoly (approximationLowCert a) u := by
    exact_mod_cast hcert
  simp only [approximationLowCert, approximationLowGapNum,
    approximationLowGapDen, evalPoly_polyAdd, evalPoly_polyScale,
    evalPoly_polyMul] at hc
  push_cast at hc ⊢
  apply ratio_gap_le_of_cross
    (he := by norm_num [approximationEnvelopeDen])
    (hfd := by exact_mod_cast hF)
    (hd := by exact_mod_cast hD)
  ring_nf at hc ⊢
  linarith

theorem approximationHighCert_implies_real {a : Nat} {u : Int}
    (hD : 0 < evalPoly approximationRationalDen u)
    (hcert : 0 ≤ evalPoly (approximationHighCert a) u) :
    (evalPoly approximationRationalNum u : Real) /
          evalPoly approximationRationalDen u -
        (evalPoly approximationTaylorNum u : Real) / approximationTaylorDen ≤
      (a : Real) / approximationEnvelopeDen := by
  have hT : 0 < approximationTaylorDen := by decide
  have hc : (0 : Real) ≤ evalPoly (approximationHighCert a) u := by
    exact_mod_cast hcert
  simp only [approximationHighCert, approximationHighGapNum,
    approximationHighGapDen, evalPoly_polyAdd, evalPoly_polyScale,
    evalPoly_polyMul] at hc
  push_cast at hc ⊢
  apply ratio_gap_le_of_cross
    (he := by norm_num [approximationEnvelopeDen])
    (hfd := by exact_mod_cast hD)
    (hd := by exact_mod_cast hT)
  ring_nf at hc ⊢
  linarith

theorem approximationLowCert_implies_weighted {a : Nat} {u : Int}
    {alpha : Real} (halpha : 0 ≤ alpha)
    (hF : 0 < evalPoly approximationUpperDen u)
    (hD : 0 < evalPoly approximationRationalDen u)
    (hcert : 0 ≤ evalPoly (approximationLowCert a) u)
    (hscale :
      2 * (10 ^ 27 : Real) * alpha *
          ((a : Real) / approximationEnvelopeDen) ≤
        (approximationErrorNum : Real) / approximationErrorDen) :
    2 * (10 ^ 27 : Real) * alpha *
        ((evalPoly approximationUpperNum u : Real) /
            evalPoly approximationUpperDen u -
          (evalPoly approximationRationalNum u : Real) /
            evalPoly approximationRationalDen u) ≤
      (approximationErrorNum : Real) / approximationErrorDen := by
  calc
    2 * (10 ^ 27 : Real) * alpha *
          ((evalPoly approximationUpperNum u : Real) /
              evalPoly approximationUpperDen u -
            (evalPoly approximationRationalNum u : Real) /
              evalPoly approximationRationalDen u) ≤
        2 * (10 ^ 27 : Real) * alpha *
          ((a : Real) / approximationEnvelopeDen) := by
      gcongr
      exact approximationLowCert_implies_real hF hD hcert
    _ ≤ (approximationErrorNum : Real) / approximationErrorDen := hscale

theorem approximationHighCert_implies_weighted {a : Nat} {u : Int}
    {alpha : Real} (halpha : 0 ≤ alpha)
    (hD : 0 < evalPoly approximationRationalDen u)
    (hcert : 0 ≤ evalPoly (approximationHighCert a) u)
    (hscale :
      2 * (10 ^ 27 : Real) * alpha *
          ((a : Real) / approximationEnvelopeDen) ≤
        (approximationErrorNum : Real) / approximationErrorDen) :
    2 * (10 ^ 27 : Real) * alpha *
        ((evalPoly approximationRationalNum u : Real) /
            evalPoly approximationRationalDen u -
          (evalPoly approximationTaylorNum u : Real) /
            approximationTaylorDen) ≤
      (approximationErrorNum : Real) / approximationErrorDen := by
  calc
    2 * (10 ^ 27 : Real) * alpha *
          ((evalPoly approximationRationalNum u : Real) /
              evalPoly approximationRationalDen u -
            (evalPoly approximationTaylorNum u : Real) /
              approximationTaylorDen) ≤
        2 * (10 ^ 27 : Real) * alpha *
          ((a : Real) / approximationEnvelopeDen) := by
      gcongr
      exact approximationHighCert_implies_real hD hcert
    _ ≤ (approximationErrorNum : Real) / approximationErrorDen := hscale

theorem approximationLowCell_implies_weighted {hi u z a : Nat}
    (ha : approximationEnvelopeCandidate hi a)
    (hu : u ≤ hi) (hz : z ^ 2 < (u + 1) * 2 ^ 104)
    (hF : 0 < evalPoly approximationUpperDen (u : Int))
    (hD : 0 < evalPoly approximationRationalDen (u : Int))
    (hcert : 0 ≤ evalPoly (approximationLowCert a) (u : Int)) :
    2 * (10 ^ 27 : Real) * ((z : Real) / 2 ^ 100) *
        ((evalPoly approximationUpperNum (u : Int) : Real) /
            evalPoly approximationUpperDen (u : Int) -
          (evalPoly approximationRationalNum (u : Int) : Real) /
            evalPoly approximationRationalDen (u : Int)) ≤
      (approximationErrorNum : Real) / approximationErrorDen := by
  exact approximationLowCert_implies_weighted
    (alpha := (z : Real) / 2 ^ 100) (by positivity) hF hD hcert
    (approximationEnvelope_scale_real ha hu hz)

theorem approximationHighCell_implies_weighted {hi u z a : Nat}
    (ha : approximationEnvelopeCandidate hi a)
    (hu : u ≤ hi) (hz : z ^ 2 < (u + 1) * 2 ^ 104)
    (hD : 0 < evalPoly approximationRationalDen (u : Int))
    (hcert : 0 ≤ evalPoly (approximationHighCert a) (u : Int)) :
    2 * (10 ^ 27 : Real) * ((z : Real) / 2 ^ 100) *
        ((evalPoly approximationRationalNum (u : Int) : Real) /
            evalPoly approximationRationalDen (u : Int) -
          (evalPoly approximationTaylorNum (u : Int) : Real) /
            approximationTaylorDen) ≤
      (approximationErrorNum : Real) / approximationErrorDen := by
  exact approximationHighCert_implies_weighted
    (alpha := (z : Real) / 2 ^ 100) (by positivity) hD hcert
    (approximationEnvelope_scale_real ha hu hz)

end

end LnFloorCarry
