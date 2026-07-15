import LnProof.Floor.CertDefs
import LnProof.Cert.FloorCertGeLoLit
import Common.Foundation.Kronecker
import LnProof.Cert.FloorCertGeLoCover

namespace LnFloorCert
open LnYul Common.Poly

set_option maxRecDepth 100000

theorem geTN2b_eq_lit : geTN2b = geTN2bLit := by
  unfold geTN2b geTN2 geTD2 gePLOP geDLO geAZ gePPHws geQQHwlo geA96 geWLO geD8 geB2 geA2
  decide +kernel

theorem geTD2b_eq_lit : geTD2b = geTD2bLit := by
  unfold geTD2b geTD2 geDLO geQQHwlo geWLO geD8 geB2 geA2
  decide +kernel

theorem geLo_eval_eq : ∀ x : Int, evalPoly certGeLo x = evalPoly certGeLoLit x := by
  refine evalPoly_ext (B := kB) certGeLo certGeLoLit ?_ ?_ ?_
  · -- Bound `polyL1 certGeLo` via the ℓ1 homomorphism lemmas on the literal
    -- summands, closing by `exact` through the definitional equality
    -- `certGeLo ≡ polyAdd …`. `unfold certGeLo` is avoided: it forces the kernel
    -- to reduce the full construction (minutes); the `exact` defeq is lazy
    -- congruence bottoming out at `geTD2b ≡ geTD2bLit` (milliseconds).
    show polyL1 certGeLo * 2 < 2 ^ kB
    have h1 := polyL1_polyAdd
      (polyScale (EUD * (Sc : Int)) (expPolyNum geTN2bLit geTD2bLit 22))
      (polyScale (-(EUD - EUNl) * KF) (polyMul [0, 1] (polyPow geTD2bLit 22)))
    have h2 := polyL1_polyScale (EUD * (Sc : Int)) (expPolyNum geTN2bLit geTD2bLit 22)
    have h3 := polyL1_expPolyNum geTN2bLit geTD2bLit 22
    have h7 : (EUD * (Sc : Int)).natAbs * polyL1 (expPolyNum geTN2bLit geTD2bLit 22) ≤
        (EUD * (Sc : Int)).natAbs *
          Common.Exp.expNum 22 (polyL1 geTN2bLit) (polyL1 geTD2bLit) :=
      Nat.mul_le_mul_left _ h3
    have h4 := polyL1_polyScale (-(EUD - EUNl) * KF) (polyMul [0, 1] (polyPow geTD2bLit 22))
    have h5 := polyL1_polyMul ([0, 1] : List Int) (polyPow geTD2bLit 22)
    have h6 := polyL1_polyPow geTD2bLit 22
    have h8 : polyL1 ([0, 1] : List Int) * polyL1 (polyPow geTD2bLit 22) ≤
        polyL1 ([0, 1] : List Int) * polyL1 geTD2bLit ^ 22 :=
      Nat.mul_le_mul_left _ h6
    have h9 : (-(EUD - EUNl) * KF).natAbs * polyL1 (polyMul ([0, 1] : List Int)
        (polyPow geTD2bLit 22)) ≤
        (-(EUD - EUNl) * KF).natAbs *
          (polyL1 ([0, 1] : List Int) * polyL1 geTD2bLit ^ 22) :=
      Nat.mul_le_mul_left _ (Nat.le_trans h5 h8)
    have hfin : ((EUD * (Sc : Int)).natAbs *
        Common.Exp.expNum 22 (polyL1 geTN2bLit) (polyL1 geTD2bLit) +
        (-(EUD - EUNl) * KF).natAbs *
          (polyL1 ([0, 1] : List Int) * polyL1 geTD2bLit ^ 22)) * 2 < 2 ^ kB := by
      decide +kernel
    have hA := Nat.le_trans h2 h7
    have hB := Nat.le_trans h4 h9
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 2 (Nat.le_trans h1 (Nat.add_le_add hA hB))) hfin
  · show polyL1 certGeLoLit * 2 < 2 ^ kB
    decide +kernel
  · show evalPoly certGeLo ((2 : Int) ^ kB) = evalPoly certGeLoLit ((2 : Int) ^ kB)
    rw [int_two_pow kB]
    unfold certGeLo
    rw [geTN2b_eq_lit, geTD2b_eq_lit]
    simp only [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyMul,
      evalPoly_polyPow, evalPoly_expPolyNum, eval01]
    decide +kernel

theorem geLo_nonnegOn :
    NonnegOn certGeLo 56022770974786139918731938273 79228162514264337593543950335 := by
  intro m h1 h2
  rw [geLo_eval_eq m]
  exact certGeLoLit_nonnegOn m h1 h2

end LnFloorCert
