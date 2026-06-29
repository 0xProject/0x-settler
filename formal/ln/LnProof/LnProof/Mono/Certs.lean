import LnProof.Model.Body
import Common.Foundation.Poly

/-!
# Decidable certificates

The analytic components of the within-octave step inequality, reduced to polynomial
nonnegativity over `[0, Uc]` and checked by the kernel through the adaptive
bisection checker. `G1`/`G2` encode the cross-multiplied worst-case step
inequalities (worst `|z| = Zc`, worst truncation slops); `certP`/`certQ` give
the polynomial-side sign facts.
-/

namespace LnYul

open Common.Poly

def UcI : Int := 2332259347626381040680638252
def ZcI : Int := 217494458298375249691265569570

/-- `-QQ(v)` -/
def nQQp : List Int := polyNeg QQc
/-- `PP(v+1)` -/
def PPs : List Int := polyCompAdd1 PPc
/-- `-QQ(v+1)` -/
def nQQs : List Int := polyNeg (polyCompAdd1 QQc)
/-- `-QQ(v+1) + SLOPQc` -/
def nQQsS : List Int := polyAdd nQQs [SLOPQc]
/-- `PP(v+1) - SLOPPc` -/
def PPsS : List Int := polyAdd PPs [-SLOPPc]

/-- Coefficient of `w` in the positive-branch step inequality. -/
def Bpoly : List Int := polySub (polyMul PPc nQQsS) (polyMul PPsS nQQp)
def RHS0 : List Int := polyMul PPc nQQsS
def G1 : List Int := polyAdd RHS0 (polyScale (-ZcI) Bpoly)
def RHS02 : List Int := polyMul PPsS nQQp
def G2 : List Int := polyAdd RHS02 (polyScale (-ZcI) Bpoly)

def certP : List Int := polyAdd PPc [-SLOPPc]
def certQ : List Int := polyAdd (polyNeg QQc) [-SLOPQc]

theorem certP_check : checkNonneg certP 0 UcI 40 = true := by decide
theorem certQ_check : checkNonneg certQ 0 UcI 40 = true := by decide
theorem G1_check : checkNonneg G1 0 (UcI - 1) 40 = true := by decide
theorem G2_check : checkNonneg G2 0 (UcI - 1) 40 = true := by decide

/-! ## Unpacked corollaries -/

theorem certP_all {v : Int} (h0 : 0 ≤ v) (h1 : v ≤ UcI) :
    SLOPPc ≤ evalPoly PPc v := by
  have h := checkNonneg_sound certP 40 0 UcI (by omega) certP_check v h0 h1
  unfold certP at h
  rw [evalPoly_polyAdd, evalPoly_singleton] at h
  omega

theorem certQ_all {v : Int} (h0 : 0 ≤ v) (h1 : v ≤ UcI) :
    SLOPQc ≤ -evalPoly QQc v := by
  have h := checkNonneg_sound certQ 40 0 UcI (by omega) certQ_check v h0 h1
  unfold certQ at h
  rw [evalPoly_polyAdd, evalPoly_singleton, evalPoly_polyNeg] at h
  omega

theorem G1_unpack (v : Int) :
    evalPoly G1 v =
      evalPoly PPc v * (-evalPoly QQc (v + 1) + SLOPQc) +
        -ZcI *
          (evalPoly PPc v * (-evalPoly QQc (v + 1) + SLOPQc) -
            (evalPoly PPc (v + 1) + -SLOPPc) * -evalPoly QQc v) := by
  unfold G1 RHS0 Bpoly PPsS nQQsS nQQs PPs nQQp
  simp only [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polySub,
    evalPoly_polyMul, evalPoly_polyNeg, evalPoly_polyCompAdd1, evalPoly_singleton]

theorem G2_unpack (v : Int) :
    evalPoly G2 v =
      (evalPoly PPc (v + 1) + -SLOPPc) * -evalPoly QQc v +
        -ZcI *
          (evalPoly PPc v * (-evalPoly QQc (v + 1) + SLOPQc) -
            (evalPoly PPc (v + 1) + -SLOPPc) * -evalPoly QQc v) := by
  unfold G2 RHS02 Bpoly PPsS nQQsS nQQs PPs nQQp
  simp only [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polySub,
    evalPoly_polyMul, evalPoly_polyNeg, evalPoly_polyCompAdd1, evalPoly_singleton]

theorem G1_all {v : Int} (h0 : 0 ≤ v) (h1 : v ≤ UcI - 1) :
    0 ≤ evalPoly PPc v * (-evalPoly QQc (v + 1) + SLOPQc) +
        -ZcI *
          (evalPoly PPc v * (-evalPoly QQc (v + 1) + SLOPQc) -
            (evalPoly PPc (v + 1) + -SLOPPc) * -evalPoly QQc v) := by
  have h := checkNonneg_sound G1 40 0 (UcI - 1) (by omega) G1_check v h0 h1
  rw [G1_unpack] at h
  exact h

theorem G2_all {v : Int} (h0 : 0 ≤ v) (h1 : v ≤ UcI - 1) :
    0 ≤ (evalPoly PPc (v + 1) + -SLOPPc) * -evalPoly QQc v +
        -ZcI *
          (evalPoly PPc v * (-evalPoly QQc (v + 1) + SLOPQc) -
            (evalPoly PPc (v + 1) + -SLOPPc) * -evalPoly QQc v) := by
  have h := checkNonneg_sound G2 40 0 (UcI - 1) (by omega) G2_check v h0 h1
  rw [G2_unpack] at h
  exact h

end LnYul
