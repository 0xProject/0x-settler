import LnProof.Cert.ErrCertGe
import LnProof.Floor.CertGeLo
import LnProof.Error.FactoredCap

/-!
# Bridge from the ge error cell cover to the `sumGE` inequality

`errGe_nonnegOn` proves `0 ≤ evalPoly certErrGeLit m` over the ge domain. Here we
identify the literal cert with the symbolic margin
`certErrGe = expMarginPoly 22 geTN2b geTD2b (errGeK·(m+1)) errGeW`
(an `evalPoly_ext` identity, exactly as `geLo_eval_eq`), and feed the existing
`sumGE_of_expMarginPoly` to obtain the `sumGE`-shaped budget inequality that
`ge_pos_cut_reduced` consumes.

The constants are the octave-extracted cell parameters at
`lnErrorBoundNum = 1692115493`:
`errGeK = 10^31·(10^18·10^42)·lnErrQ·(10^40+160)`,
`errGeW = BIASCAPNUM·(lnErrQ+minPosAvail)·wadRayStrictDen·10^40`.
-/

namespace LnFloorCert

open LnYul Common.Poly Common.Exp

set_option maxRecDepth 100000

def errGeK : Int :=
  63382530011411470074835160268800000001014120480182583521197362564300800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

/-- `errGeW = BIASCAPNUM · (lnErrQ + minPosAvailGe) · wadRayStrictDen · 10^40`,
where `minPosAvailGe = 692115493·2^99 + 2^27·10^9` is the GE-internal bound
(1.692115493 ulp) used by the ge cells, tighter than the
published bound, so the ge branch only tracks the bias here. -/
def errGeW : Nat :=
  biasCapNum *
    (lnErrQ + (692115493 * 2 ^ 99 + 2 ^ 27 * 10 ^ 9)) * wadRayStrictDen * 10 ^ 40

def certErrGe : List Int :=
  expMarginPoly 22 geTN2b geTD2b (polyScale errGeK [1, 1]) errGeW

theorem errGe_eval_eq : ∀ x : Int, evalPoly certErrGe x = evalPoly certErrGeLit x := by
  refine evalPoly_ext (B := kB) certErrGe certErrGeLit ?_ ?_ ?_
  · -- polyL1 bound on the symbolic margin, via the ℓ1 homomorphism lemmas on the
    -- degree-12 literal bases; the full degree-221 poly is never reduced.
    show polyL1 certErrGe * 2 < 2 ^ kB
    have hadd := polyL1_polyAdd
      (polyScale errGeW (expPolyNum geTN2bLit geTD2bLit 22))
      (polyNeg (polyScale (fact 22 : Int)
        (polyMul (polyScale errGeK [1, 1]) (polyPow geTD2bLit 22))))
    have hneg := polyL1_polyNeg
      (polyScale (fact 22 : Int)
        (polyMul (polyScale errGeK [1, 1]) (polyPow geTD2bLit 22)))
    have hA := polyL1_polyScale errGeW (expPolyNum geTN2bLit geTD2bLit 22)
    have hAe := polyL1_expPolyNum geTN2bLit geTD2bLit 22
    have hA2 : (errGeW : Int).natAbs * polyL1 (expPolyNum geTN2bLit geTD2bLit 22) ≤
        (errGeW : Int).natAbs * expNum 22 (polyL1 geTN2bLit) (polyL1 geTD2bLit) :=
      Nat.mul_le_mul_left _ hAe
    have hB := polyL1_polyScale (fact 22 : Int)
      (polyMul (polyScale errGeK [1, 1]) (polyPow geTD2bLit 22))
    have hBm := polyL1_polyMul (polyScale errGeK [1, 1]) (polyPow geTD2bLit 22)
    have hBs := polyL1_polyScale errGeK ([1, 1] : List Int)
    have hBp := polyL1_polyPow geTD2bLit 22
    have hBm2 : polyL1 (polyScale errGeK [1, 1]) * polyL1 (polyPow geTD2bLit 22) ≤
        errGeK.natAbs * polyL1 ([1, 1] : List Int) * polyL1 geTD2bLit ^ 22 :=
      Nat.mul_le_mul hBs hBp
    have hB2 : (fact 22 : Int).natAbs *
        polyL1 (polyMul (polyScale errGeK [1, 1]) (polyPow geTD2bLit 22)) ≤
        (fact 22 : Int).natAbs *
          (errGeK.natAbs * polyL1 ([1, 1] : List Int) * polyL1 geTD2bLit ^ 22) :=
      Nat.mul_le_mul_left _ (Nat.le_trans hBm hBm2)
    have hfin : ((errGeW : Int).natAbs *
          expNum 22 (polyL1 geTN2bLit) (polyL1 geTD2bLit) +
        (fact 22 : Int).natAbs *
          (errGeK.natAbs * polyL1 ([1, 1] : List Int) * polyL1 geTD2bLit ^ 22)) * 2
          < 2 ^ kB := by
      decide +kernel
    have hAfin := Nat.le_trans hA hA2
    have hBfin := Nat.le_trans hB hB2
    rw [hneg] at hadd
    exact Nat.lt_of_le_of_lt
      (Nat.mul_le_mul_right 2 (Nat.le_trans hadd (Nat.add_le_add hAfin hBfin))) hfin
  · show polyL1 certErrGeLit * 2 < 2 ^ kB
    decide +kernel
  · show evalPoly certErrGe ((2 : Int) ^ kB) = evalPoly certErrGeLit ((2 : Int) ^ kB)
    rw [int_two_pow kB]
    unfold certErrGe expMarginPoly
    rw [geTN2b_eq_lit, geTD2b_eq_lit]
    simp only [evalPoly_polySub, evalPoly_polyScale, evalPoly_polyMul,
      evalPoly_polyPow, evalPoly_expPolyNum, eval01]
    decide +kernel

theorem certErrGe_nonnegOn :
    NonnegOn certErrGe 56022770974786139918731938273 79228162514264337593543950335 := by
  intro x hlo hhi
  rw [errGe_eval_eq]
  exact errGe_nonnegOn x hlo hhi

/-- The ge cell cover proves the `sumGE`-shaped budget inequality. -/
theorem errGe_sumGE {m : Nat} (h1 : Sc + 46 ≤ m) (h2 : m < MHI) :
    sumGE 22 (evalPoly geTN2b (m : Int)).toNat (evalPoly geTD2b (m : Int)).toNat
      (evalPoly (polyScale errGeK [1, 1]) (m : Int)).toNat errGeW := by
  have hge : (56022770974786139918731938273 : Int) ≤ (m : Int) := by
    simp only [Sc] at h1; omega
  have hle : (m : Int) ≤ 79228162514264337593543950335 := by
    simp only [MHI] at h2; omega
  have hnn : 0 ≤ evalPoly certErrGe (m : Int) := certErrGe_nonnegOn _ hge hle
  have hyp : 0 ≤ evalPoly (polyScale errGeK [1, 1]) (m : Int) := by
    rw [evalPoly_polyScale]
    refine Int.mul_nonneg (by unfold errGeK; decide) ?_
    have hm : (0 : Int) ≤ (m : Int) := Int.ofNat_nonneg m
    simp only [evalPoly, Int.mul_zero, Int.add_zero, Int.mul_one]
    omega
  exact sumGE_of_expMarginPoly hnn
    (Int.toNat_of_nonneg (geTN2b_nonneg_of_outer h1 h2)).symm
    (Int.toNat_of_nonneg (Int.le_of_lt (geTD2b_pos_of_outer h1 h2))).symm
    (Int.toNat_of_nonneg hyp).symm

end LnFloorCert
