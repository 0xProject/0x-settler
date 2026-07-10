import LnProof.Floor.CertDefs
import LnProof.Cert.FloorCertGeLoLit
import Common.Foundation.Kronecker
import LnProof.Cert.FloorCertGeLoC00
import LnProof.Cert.FloorCertGeLoC01
import LnProof.Cert.FloorCertGeLoC02
import LnProof.Cert.FloorCertGeLoC03
import LnProof.Cert.FloorCertGeLoC04
import LnProof.Cert.FloorCertGeLoC05
import LnProof.Cert.FloorCertGeLoC06
import LnProof.Cert.FloorCertGeLoC07
import LnProof.Cert.FloorCertGeLoC08
import LnProof.Cert.FloorCertGeLoC09
import LnProof.Cert.FloorCertGeLoC10
import LnProof.Cert.FloorCertGeLoC11
import LnProof.Cert.FloorCertGeLoC12
import LnProof.Cert.FloorCertGeLoC13
import LnProof.Cert.FloorCertGeLoC14
import LnProof.Cert.FloorCertGeLoC15

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
  have hev := geLo_eval_eq m
  rw [hev]
  rcases Int.lt_or_le m (62244752178564837341413711044 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell00 m (by omega) (by omega)
  rcases Int.lt_or_le m (63021047966864144477302463709 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell01 m (by omega) (by omega)
  rcases Int.lt_or_le m (63732504204331280578284050406 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell02 m (by omega) (by omega)
  rcases Int.lt_or_le m (68555078677578616072739796057 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell03 m (by omega) (by omega)
  rcases Int.lt_or_le m (69188950000471302436179690222 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell04 m (by omega) (by omega)
  rcases Int.lt_or_le m (69421653762451729097000721095 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell05 m (by omega) (by omega)
  rcases Int.lt_or_le m (73730556485602365085160742340 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell06 m (by omega) (by omega)
  rcases Int.lt_or_le m (74329863996105955191718353701 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell07 m (by omega) (by omega)
  rcases Int.lt_or_le m (74464216934146832631101548902 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell08 m (by omega) (by omega)
  rcases Int.lt_or_le m (74624338318165849272995850728 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell09 m (by omega) (by omega)
  rcases Int.lt_or_le m (77449142725659361688692863981 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell10 m (by omega) (by omega)
  rcases Int.lt_or_le m (77854395661672196008615607277 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell11 m (by omega) (by omega)
  rcases Int.lt_or_le m (77938896631029212070537782373 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell12 m (by omega) (by omega)
  rcases Int.lt_or_le m (77976060836007440768847374767 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell13 m (by omega) (by omega)
  rcases Int.lt_or_le m (78012383942778533660629771928 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell14 m (by omega) (by omega)
  exact checkCoverK_sound _ _ _ _ _ geLo_cell15 m (by omega) h2

theorem geLo_nonneg {m : Int} (h1 : 56022770974786139918731938273 ≤ m)
    (h2 : m ≤ 79228162514264337593543950335) : 0 ≤ evalPoly certGeLo m :=
  geLo_nonnegOn m h1 h2

end LnFloorCert
