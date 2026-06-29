import LnProof.Floor.CertDefs
import LnProof.Cert.FloorCertLit
import Common.Foundation.Kronecker
import LnProof.Cert.FloorCertLtUpC00
import LnProof.Cert.FloorCertLtUpC01
import LnProof.Cert.FloorCertLtUpC02
import LnProof.Cert.FloorCertLtUpC03
import LnProof.Cert.FloorCertLtUpC04
import LnProof.Cert.FloorCertLtUpC05
import LnProof.Cert.FloorCertLtUpC06
import LnProof.Cert.FloorCertLtUpC07
import LnProof.Cert.FloorCertLtUpC08
import LnProof.Cert.FloorCertLtUpC09
import LnProof.Cert.FloorCertLtUpC10
import LnProof.Cert.FloorCertLtUpC11
import LnProof.Cert.FloorCertLtUpC12
import LnProof.Cert.FloorCertLtUpC13
import LnProof.Cert.FloorCertLtUpC14
import LnProof.Cert.FloorCertLtUpC15
import LnProof.Cert.FloorCertLtUpC16

namespace LnFloorCert
open LnYul Common.Poly

set_option maxRecDepth 100000

theorem ltTN2b_eq_lit : ltTN2b = ltTN2bLit := by
  unfold ltTN2b ltTN2 ltTD2 ltPLOP ltDLO ltAZ ltPPHws ltQQHwlo ltA96 ltWLO ltD8 ltB2 ltA2
  decide +kernel

theorem ltTD2b_eq_lit : ltTD2b = ltTD2bLit := by
  unfold ltTD2b ltTD2 ltDLO ltQQHwlo ltWLO ltD8 ltB2 ltA2
  decide +kernel

theorem ltUp_eval_eq : ∀ x : Int, evalPoly certLtUp x = evalPoly certLtUpLit x := by
  refine evalPoly_ext (B := kB) certLtUp certLtUpLit ?_ ?_ ?_
  · -- Bound `polyL1 certLtUp` via the ℓ1 homomorphism lemmas on the literal
    -- summands, closing by `exact` through the definitional equality
    -- `certLtUp ≡ polyAdd …`. `unfold certLtUp` is avoided: it forces the kernel
    -- to reduce the full construction (minutes); the `exact` defeq is lazy
    -- congruence bottoming out at `ltTD2b ≡ ltTD2bLit` (milliseconds).
    show polyL1 certLtUp * 2 < 2 ^ kB
    have h1 := polyL1_polyAdd
      (polyScale (EUD + EUN) (polyMul [0, 1] (expPolyNum ltTN2bLit ltTD2bLit 22)))
      (polyScale (-EUD * (Sc : Int) * KF) (polyPow ltTD2bLit 22))
    have h2 := polyL1_polyScale (EUD + EUN) (polyMul [0, 1] (expPolyNum ltTN2bLit ltTD2bLit 22))
    have h3 := polyL1_polyMul ([0, 1] : List Int) (expPolyNum ltTN2bLit ltTD2bLit 22)
    have h4 := polyL1_expPolyNum ltTN2bLit ltTD2bLit 22
    have h5 : polyL1 ([0, 1] : List Int) * polyL1 (expPolyNum ltTN2bLit ltTD2bLit 22) ≤
        polyL1 ([0, 1] : List Int) * Common.Exp.expNum 22 (polyL1 ltTN2bLit) (polyL1 ltTD2bLit) :=
      Nat.mul_le_mul_left _ h4
    have h6 : (EUD + EUN).natAbs * polyL1 (polyMul ([0, 1] : List Int) (expPolyNum ltTN2bLit ltTD2bLit 22)) ≤
        (EUD + EUN).natAbs * (polyL1 ([0, 1] : List Int) * Common.Exp.expNum 22 (polyL1 ltTN2bLit) (polyL1 ltTD2bLit)) :=
      Nat.mul_le_mul_left _ (Nat.le_trans h3 h5)
    have h7 := polyL1_polyScale (-EUD * (Sc : Int) * KF) (polyPow ltTD2bLit 22)
    have h8 := polyL1_polyPow ltTD2bLit 22
    have h9 : (-EUD * (Sc : Int) * KF).natAbs * polyL1 (polyPow ltTD2bLit 22) ≤
        (-EUD * (Sc : Int) * KF).natAbs * polyL1 ltTD2bLit ^ 22 :=
      Nat.mul_le_mul_left _ h8
    have hfin : ((EUD + EUN).natAbs * (polyL1 ([0, 1] : List Int) * Common.Exp.expNum 22 (polyL1 ltTN2bLit) (polyL1 ltTD2bLit)) +
        (-EUD * (Sc : Int) * KF).natAbs * polyL1 ltTD2bLit ^ 22) * 2 < 2 ^ kB := by
      decide +kernel
    have hA := Nat.le_trans h2 h6
    have hB := Nat.le_trans h7 h9
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 2 (Nat.le_trans h1 (Nat.add_le_add hA hB))) hfin
  · show polyL1 certLtUpLit * 2 < 2 ^ kB
    decide +kernel
  · show evalPoly certLtUp ((2 : Int) ^ kB) = evalPoly certLtUpLit ((2 : Int) ^ kB)
    rw [int_two_pow kB]
    unfold certLtUp
    rw [ltTN2b_eq_lit, ltTD2b_eq_lit]
    simp only [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyMul,
      evalPoly_polyPow, evalPoly_expPolyNum, eval01]
    decide +kernel

theorem ltUp_nonneg {m : Int} (h1 : 39614081257132168796771975168 ≤ m) (h2 : m ≤ 56022770974786139918731938181) :
    0 ≤ evalPoly certLtUp m := by
  have hev := ltUp_eval_eq m
  rw [hev]
  rcases Int.lt_or_le m (39982094489912265292386939330 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell00 m (by omega) (by omega)
  rcases Int.lt_or_le m (40149298654143480131116927797 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell01 m (by omega) (by omega)
  rcases Int.lt_or_le m (40201343509165054248704163767 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell02 m (by omega) (by omega)
  rcases Int.lt_or_le m (40224348129155411324248597878 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell03 m (by omega) (by omega)
  rcases Int.lt_or_le m (40237671635020882839496520159 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell04 m (by omega) (by omega)
  rcases Int.lt_or_le m (40258748239835768207775715658 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell05 m (by omega) (by omega)
  rcases Int.lt_or_le m (41686814657515192596739173673 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell06 m (by omega) (by omega)
  rcases Int.lt_or_le m (42010208390739198067655462807 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell07 m (by omega) (by omega)
  rcases Int.lt_or_le m (42091380544708413934368876661 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell08 m (by omega) (by omega)
  rcases Int.lt_or_le m (42146662162229712555615056322 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell09 m (by omega) (by omega)
  rcases Int.lt_or_le m (44752276460150783290898176684 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell10 m (by omega) (by omega)
  rcases Int.lt_or_le m (45171106034455008017766705000 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell11 m (by omega) (by omega)
  rcases Int.lt_or_le m (45304867147592323391712272578 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell12 m (by omega) (by omega)
  rcases Int.lt_or_le m (49088688274983454610883926975 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell13 m (by omega) (by omega)
  rcases Int.lt_or_le m (49644314882674105514797500243 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell14 m (by omega) (by omega)
  rcases Int.lt_or_le m (50222365124295153396878600218 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell15 m (by omega) (by omega)
  exact checkCoverK_sound _ _ _ _ _ ltUp_cell16 m (by omega) h2

end LnFloorCert
