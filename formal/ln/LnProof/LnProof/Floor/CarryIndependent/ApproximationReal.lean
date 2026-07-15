import LnProof.Floor.CarryIndependent.ApproximationSound
import LnProof.Floor.CarryIndependent.Atanh
import LnProof.Mono.Certs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

open scoped BigOperators

namespace LnFloorCarry

open Finset Common.Poly LnYul

set_option maxRecDepth 100000

noncomputable section

private theorem evalPoly_append (p q : List Int) (x : Int) :
    evalPoly (p ++ q) x = evalPoly p x + x ^ p.length * evalPoly q x := by
  induction p with
  | nil => simp [evalPoly]
  | cons c p ih =>
      simp only [List.cons_append, evalPoly, List.length_cons, ih]
      rw [pow_succ]
      ring

private theorem evalPoly_map_range (f : Nat → Int) (n : Nat) (x : Int) :
    evalPoly ((List.range n).map f) x =
      ∑ j ∈ range n, f j * x ^ j := by
  induction n with
  | zero => simp [evalPoly]
  | succ n ih =>
      simp only [List.range_succ, List.map_append, List.map_singleton,
        evalPoly_append, List.length_map, List.length_range, ih, evalPoly,
        Finset.sum_range_succ]
      ring

private theorem evalPoly_replicate_zero (n : Nat) (x : Int) :
    evalPoly (List.replicate n 0) x = 0 := by
  induction n with
  | zero => simp [evalPoly]
  | succ n ih =>
      rw [List.replicate_succ, evalPoly, ih]
      ring

private theorem evalPoly_tailPower (n : Nat) (x : Int) :
    evalPoly (List.replicate n 0 ++ [1]) x = x ^ n := by
  rw [evalPoly_append, evalPoly_replicate_zero]
  simp [evalPoly]

private theorem evalPoly_oneMinus (x : Int) :
    evalPoly approximationOneMinus x = (approximationScale : Int) - x := by
  simp [approximationOneMinus, evalPoly, sub_eq_add_neg]

private theorem approximationOddProduct_eq_prod :
    approximationOddProduct =
      ((List.range approximationTerms).map fun j : Nat =>
        2 * (j : Int) + 1).prod := by
  unfold approximationOddProduct
  symm
  rw [List.prod_eq_foldl, List.foldl_map]

private theorem oddFactorList_pos (l : List Nat) :
    0 < (l.map fun j : Nat => 2 * (j : Int) + 1).prod := by
  induction l with
  | nil => simp
  | cons j l ih =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_pos (by omega) ih

private theorem approximationOddProduct_pos : 0 < approximationOddProduct := by
  rw [approximationOddProduct_eq_prod]
  exact oddFactorList_pos _

private theorem approximationOddFactor_dvd {j : Nat}
    (hj : j < approximationTerms) :
    2 * (j : Int) + 1 ∣ approximationOddProduct := by
  rw [approximationOddProduct_eq_prod]
  apply List.dvd_prod
  exact List.mem_map_of_mem (List.mem_range.mpr hj)

private theorem approximationTaylor_term_identity
    {q p scale value factor : Real} {a b j : Nat}
    (hp : p ≠ 0) (hscale : scale ≠ 0) (hfactor : factor ≠ 0)
    (hquotient : q * factor = p) (hexponent : a + j = b) :
    (85 * q * scale ^ a * value ^ j) / (85 * p * scale ^ b) =
      (value / scale) ^ j / factor := by
  rw [div_pow, div_div]
  apply (div_eq_div_iff
    (mul_ne_zero (mul_ne_zero (by norm_num) hp) (pow_ne_zero _ hscale))
    (mul_ne_zero (pow_ne_zero _ hscale) hfactor)).2
  rw [← hexponent, pow_add, ← hquotient]
  ring

theorem approximationTaylor_eval (u : Nat) :
    (evalPoly approximationTaylorNum (u : Int) : Real) /
        approximationTaylorDen =
      ∑ j ∈ range approximationTerms,
        ((u : Real) / approximationScale) ^ j / (2 * j + 1) := by
  rw [approximationTaylorNum, evalPoly_map_range, approximationTaylorDen]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < approximationTerms := Finset.mem_range.mp hj
  have hquotientI :
      (approximationOddProduct / (2 * (j : Int) + 1)) *
          (2 * (j : Int) + 1) = approximationOddProduct :=
    Int.ediv_mul_cancel (approximationOddFactor_dvd hjlt)
  have hquotientR :
      ((approximationOddProduct / (2 * (j : Int) + 1) : Int) : Real) *
          (2 * (j : Real) + 1) = approximationOddProduct := by
    exact_mod_cast hquotientI
  have hp : (approximationOddProduct : Real) ≠ 0 := by
    exact_mod_cast approximationOddProduct_pos.ne'
  have hscale : (approximationScale : Real) ≠ 0 := by
    norm_num [approximationScale]
  have hfactor : (2 * (j : Real) + 1) ≠ 0 := by positivity
  have hexponent :
      approximationTerms - 1 - j + j = approximationTerms - 1 := by
    omega
  exact approximationTaylor_term_identity hp hscale hfactor hquotientR hexponent

theorem approximationUpper_eval (u : Nat) (hu : u < approximationScale) :
    (evalPoly approximationUpperNum (u : Int) : Real) /
        evalPoly approximationUpperDen (u : Int) =
      (∑ j ∈ range approximationTerms,
          ((u : Real) / approximationScale) ^ j / (2 * j + 1)) +
        ((u : Real) / approximationScale) ^ approximationTerms /
          ((2 * approximationTerms + 1) *
            (1 - (u : Real) / approximationScale)) := by
  have hTaylor := approximationTaylor_eval u
  have hTaylorDen : (approximationTaylorDen : Real) ≠ 0 := by
    exact_mod_cast (show approximationTaylorDen ≠ 0 by decide)
  have hScale : (approximationScale : Real) ≠ 0 := by
    norm_num [approximationScale]
  have hGap : (approximationScale : Real) - u ≠ 0 := by
    have huR : (u : Real) < approximationScale := by exact_mod_cast hu
    linarith
  simp only [approximationUpperNum, approximationUpperDen,
    evalPoly_polyAdd, evalPoly_polyMul, evalPoly_polyScale,
    evalPoly_oneMinus, approximationTailPower, evalPoly_tailPower]
  push_cast
  rw [← hTaylor]
  field_simp [hTaylorDen, hScale, hGap];
    norm_num [approximationTaylorDen, approximationOddProduct,
    approximationScale, approximationTerms]; ring

theorem approximationUpperDen_pos {u : Nat} (hu : u ≤ approximationMaxU) :
    0 < evalPoly approximationUpperDen (u : Int) := by
  have hTaylorDen : 0 < approximationTaylorDen := by decide
  have huScale : u < approximationScale :=
    hu.trans_lt (by decide)
  have huScaleI : (u : Int) < approximationScale := by exact_mod_cast huScale
  simp only [approximationUpperDen, evalPoly_polyScale,
    evalPoly_oneMinus]
  exact Int.mul_pos hTaylorDen (by omega)

theorem approximationRationalDen_pos {u : Nat} (hu : u ≤ approximationMaxU) :
    0 < evalPoly approximationRationalDen (u : Int) := by
  have huCast : (u : Int) ≤ (approximationMaxU : Int) := by
    exact_mod_cast hu
  have huI : (u : Int) ≤ UcI := by
    simpa [approximationMaxU, Uc, UcI] using huCast
  have hq := certQ_all (v := (u : Int)) (by positivity) huI
  have hslop : 0 < SLOPQc := by norm_num [SLOPQc]
  simp only [approximationRationalDen, evalPoly_polyNeg]
  omega

theorem approximationRational_eval (u : Nat) (hu : u ≤ approximationMaxU) :
    (evalPoly approximationRationalNum (u : Int) : Real) /
        evalPoly approximationRationalDen (u : Int) =
      ((evalPoly PPc (u : Int) : Real) / 2 ^ 358) /
        ((-evalPoly QQc (u : Int) : Int) / 2 ^ 386) := by
  have hden := approximationRationalDen_pos hu
  have hq : (0 : Real) < (-evalPoly QQc (u : Int) : Int) := by
    rw [approximationRationalDen, evalPoly_polyNeg] at hden
    exact_mod_cast hden
  have h358 : (2 ^ 358 : Real) ≠ 0 := by positivity
  have h386 : (2 ^ 386 : Real) ≠ 0 := by positivity
  have hqScaled : ((-evalPoly QQc (u : Int) : Int) / (2 ^ 386 : Real)) ≠ 0 :=
    div_ne_zero hq.ne' h386
  simp only [approximationRationalNum, approximationRationalDen,
    evalPoly_polyScale, evalPoly_polyNeg]
  push_cast at hq hqScaled ⊢
  apply (div_eq_div_iff hq.ne' hqScaled).2
  field_simp [h358, h386]; norm_num; ring

theorem approximationLowCell_implies_series_eval_bound {hi u z a : Nat}
    (ha : approximationEnvelopeCandidate hi a)
    (hu : u ≤ hi) (huMax : u ≤ approximationMaxU)
    (hz : z ^ 2 < (u + 1) * 2 ^ 104)
    (hcert : 0 ≤ evalPoly (approximationLowCert a) (u : Int)) :
    2 * (10 ^ 27 : Real) * ((z : Real) / 2 ^ 100) *
        ((∑' j : Nat,
            ((u : Real) / approximationScale) ^ j / (2 * j + 1)) -
          (evalPoly approximationRationalNum (u : Int) : Real) /
            evalPoly approximationRationalDen (u : Int)) ≤
      (approximationErrorNum : Real) / approximationErrorDen := by
  have huScale : u < approximationScale := huMax.trans_lt (by decide)
  have hv0 : (0 : Real) ≤ (u : Real) / approximationScale := by positivity
  have hv1 : (u : Real) / approximationScale < 1 := by
    rw [div_lt_one (by norm_num [approximationScale])]
    exact_mod_cast huScale
  have hseries := series_le_partial_geometric hv0 hv1 approximationTerms
  have hupper := approximationUpper_eval u huScale
  have hseriesUpper :
      (∑' j : Nat,
          ((u : Real) / approximationScale) ^ j / (2 * j + 1)) ≤
        (evalPoly approximationUpperNum (u : Int) : Real) /
          evalPoly approximationUpperDen (u : Int) := by
    rw [hupper]
    exact hseries
  have hbound := approximationLowCell_implies_weighted ha hu hz
    (approximationUpperDen_pos huMax) (approximationRationalDen_pos huMax) hcert
  calc
    2 * (10 ^ 27 : Real) * ((z : Real) / 2 ^ 100) *
          ((∑' j : Nat,
              ((u : Real) / approximationScale) ^ j / (2 * j + 1)) -
            (evalPoly approximationRationalNum (u : Int) : Real) /
              evalPoly approximationRationalDen (u : Int)) ≤
        2 * (10 ^ 27 : Real) * ((z : Real) / 2 ^ 100) *
          ((evalPoly approximationUpperNum (u : Int) : Real) /
              evalPoly approximationUpperDen (u : Int) -
            (evalPoly approximationRationalNum (u : Int) : Real) /
              evalPoly approximationRationalDen (u : Int)) := by
      exact mul_le_mul_of_nonneg_left
        (sub_le_sub_right hseriesUpper _) (by positivity)
    _ ≤ (approximationErrorNum : Real) / approximationErrorDen := hbound

theorem approximationHighCell_implies_series_eval_bound {hi u z a : Nat}
    (ha : approximationEnvelopeCandidate hi a)
    (hu : u ≤ hi) (huMax : u ≤ approximationMaxU)
    (hz : z ^ 2 < (u + 1) * 2 ^ 104)
    (hcert : 0 ≤ evalPoly (approximationHighCert a) (u : Int)) :
    2 * (10 ^ 27 : Real) * ((z : Real) / 2 ^ 100) *
        ((evalPoly approximationRationalNum (u : Int) : Real) /
            evalPoly approximationRationalDen (u : Int) -
          (∑' j : Nat,
            ((u : Real) / approximationScale) ^ j / (2 * j + 1))) ≤
      (approximationErrorNum : Real) / approximationErrorDen := by
  have huScale : u < approximationScale := huMax.trans_lt (by decide)
  have hv0 : (0 : Real) ≤ (u : Real) / approximationScale := by positivity
  have hv1 : (u : Real) / approximationScale < 1 := by
    rw [div_lt_one (by norm_num [approximationScale])]
    exact_mod_cast huScale
  have hpartial := partial_le_series hv0 hv1 approximationTerms
  have hbound := approximationHighCell_implies_weighted ha hu hz
    (approximationRationalDen_pos huMax) hcert
  rw [approximationTaylor_eval] at hbound
  calc
    2 * (10 ^ 27 : Real) * ((z : Real) / 2 ^ 100) *
          ((evalPoly approximationRationalNum (u : Int) : Real) /
              evalPoly approximationRationalDen (u : Int) -
            (∑' j : Nat,
              ((u : Real) / approximationScale) ^ j / (2 * j + 1))) ≤
        2 * (10 ^ 27 : Real) * ((z : Real) / 2 ^ 100) *
          ((evalPoly approximationRationalNum (u : Int) : Real) /
              evalPoly approximationRationalDen (u : Int) -
            ∑ j ∈ range approximationTerms,
              ((u : Real) / approximationScale) ^ j / (2 * j + 1)) := by
      have hgap :
          (evalPoly approximationRationalNum (u : Int) : Real) /
                evalPoly approximationRationalDen (u : Int) -
              (∑' j : Nat,
                ((u : Real) / approximationScale) ^ j / (2 * j + 1)) ≤
            (evalPoly approximationRationalNum (u : Int) : Real) /
                evalPoly approximationRationalDen (u : Int) -
              ∑ j ∈ range approximationTerms,
                ((u : Real) / approximationScale) ^ j / (2 * j + 1) := by
        linarith
      exact mul_le_mul_of_nonneg_left hgap (by positivity)
    _ ≤ (approximationErrorNum : Real) / approximationErrorDen := hbound

theorem approximationLowCell_implies_series_bound {hi u z a : Nat}
    (ha : approximationEnvelopeCandidate hi a)
    (hu : u ≤ hi) (huMax : u ≤ approximationMaxU)
    (hz : z ^ 2 < (u + 1) * 2 ^ 104)
    (hcert : 0 ≤ evalPoly (approximationLowCert a) (u : Int)) :
    2 * (10 ^ 27 : Real) * ((z : Real) / 2 ^ 100) *
        ((∑' j : Nat,
            ((u : Real) / approximationScale) ^ j / (2 * j + 1)) -
          ((evalPoly PPc (u : Int) : Real) / 2 ^ 358) /
            ((-evalPoly QQc (u : Int) : Int) / 2 ^ 386)) ≤
      (approximationErrorNum : Real) / approximationErrorDen := by
  rw [← approximationRational_eval u huMax]
  exact approximationLowCell_implies_series_eval_bound ha hu huMax hz hcert

theorem approximationHighCell_implies_series_bound {hi u z a : Nat}
    (ha : approximationEnvelopeCandidate hi a)
    (hu : u ≤ hi) (huMax : u ≤ approximationMaxU)
    (hz : z ^ 2 < (u + 1) * 2 ^ 104)
    (hcert : 0 ≤ evalPoly (approximationHighCert a) (u : Int)) :
    2 * (10 ^ 27 : Real) * ((z : Real) / 2 ^ 100) *
        (((evalPoly PPc (u : Int) : Real) / 2 ^ 358) /
            ((-evalPoly QQc (u : Int) : Int) / 2 ^ 386) -
          (∑' j : Nat,
            ((u : Real) / approximationScale) ^ j / (2 * j + 1))) ≤
      (approximationErrorNum : Real) / approximationErrorDen := by
  rw [← approximationRational_eval u huMax]
  exact approximationHighCell_implies_series_eval_bound ha hu huMax hz hcert

end

end LnFloorCarry
