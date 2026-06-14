import LnProof.FloorCertDefs
import LnProof.FloorCertLit
import LnProof.Kronecker
import LnProof.FloorCertLtUpC00
import LnProof.FloorCertLtUpC01
import LnProof.FloorCertLtUpC02
import LnProof.FloorCertLtUpC03
import LnProof.FloorCertLtUpC04
import LnProof.FloorCertLtUpC05
import LnProof.FloorCertLtUpC06
import LnProof.FloorCertLtUpC07
import LnProof.FloorCertLtUpC08
import LnProof.FloorCertLtUpC09
import LnProof.FloorCertLtUpC10

namespace LnFloorCert
open LnGeneratedModel LnPoly

set_option maxRecDepth 100000

theorem ltTN2b_eq_lit : ltTN2b = ltTN2bLit := by
  unfold ltTN2b ltTN2 ltTD2 ltPLOP ltDLO ltAZ ltPPHws ltQQHwlo ltA96 ltWLO ltD8 ltB2 ltA2
  decide +kernel

theorem ltTD2b_eq_lit : ltTD2b = ltTD2bLit := by
  unfold ltTD2b ltTD2 ltDLO ltQQHwlo ltWLO ltD8 ltB2 ltA2
  decide +kernel

theorem ltUp_eval_eq : ∀ x : Int, evalPoly certLtUp x = evalPoly certLtUpLit x := by
  refine evalPoly_ext (B := kB) certLtUp certLtUpLit ?_ ?_ ?_
  · show polyL1 certLtUp * 2 < 2 ^ kB
    unfold certLtUp
    rw [ltTN2b_eq_lit, ltTD2b_eq_lit]
    have h1 := polyL1_polyAdd
      (polyScale (EUD + EUN) (polyMul [0, 1] (expPolyNum ltTN2bLit ltTD2bLit 22)))
      (polyScale (-EUD * (Sc : Int) * KF) (polyPow ltTD2bLit 22))
    have h2 := polyL1_polyScale (EUD + EUN) (polyMul [0, 1] (expPolyNum ltTN2bLit ltTD2bLit 22))
    have h3 := polyL1_polyMul ([0, 1] : List Int) (expPolyNum ltTN2bLit ltTD2bLit 22)
    have h4 := polyL1_expPolyNum ltTN2bLit ltTD2bLit 22
    have h5 : polyL1 ([0, 1] : List Int) * polyL1 (expPolyNum ltTN2bLit ltTD2bLit 22) ≤
        polyL1 ([0, 1] : List Int) * LnExp.expNum 22 (polyL1 ltTN2bLit) (polyL1 ltTD2bLit) :=
      Nat.mul_le_mul_left _ h4
    have h6 : (EUD + EUN).natAbs * polyL1 (polyMul ([0, 1] : List Int) (expPolyNum ltTN2bLit ltTD2bLit 22)) ≤
        (EUD + EUN).natAbs * (polyL1 ([0, 1] : List Int) * LnExp.expNum 22 (polyL1 ltTN2bLit) (polyL1 ltTD2bLit)) :=
      Nat.mul_le_mul_left _ (Nat.le_trans h3 h5)
    have h7 := polyL1_polyScale (-EUD * (Sc : Int) * KF) (polyPow ltTD2bLit 22)
    have h8 := polyL1_polyPow ltTD2bLit 22
    have h9 : (-EUD * (Sc : Int) * KF).natAbs * polyL1 (polyPow ltTD2bLit 22) ≤
        (-EUD * (Sc : Int) * KF).natAbs * polyL1 ltTD2bLit ^ 22 :=
      Nat.mul_le_mul_left _ h8
    have hfin : ((EUD + EUN).natAbs * (polyL1 ([0, 1] : List Int) * LnExp.expNum 22 (polyL1 ltTN2bLit) (polyL1 ltTD2bLit)) +
        (-EUD * (Sc : Int) * KF).natAbs * polyL1 ltTD2bLit ^ 22) * 2 < 2 ^ kB := by
      decide +kernel
    have hA := Nat.le_trans h2 h6
    have hB := Nat.le_trans h7 h9
    omega
  · show polyL1 certLtUpLit * 2 < 2 ^ kB
    decide +kernel
  · show evalPoly certLtUp ((2 : Int) ^ kB) = evalPoly certLtUpLit ((2 : Int) ^ kB)
    unfold certLtUp
    rw [ltTN2b_eq_lit, ltTD2b_eq_lit]
    simp only [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyMul,
      evalPoly_polyPow, evalPoly_expPolyNum, eval01]
    decide +kernel

theorem ltUp_nonneg {m : Int} (h1 : 10141204801825835211973625643008 ≤ m) (h2 : m ≤ 14341829369545251819195376186183) :
    0 ≤ evalPoly certLtUp m := by
  have hev := ltUp_eval_eq m
  rw [hev]
  rcases Int.lt_or_le m (10236733219469637195766410765227 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell00 m (by omega) (by omega)
  rcases Int.lt_or_le m (10283083180369672200219960462811 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell01 m (by omega) (by omega)
  rcases Int.lt_or_le m (10305530652815519157653642498119 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell02 m (by omega) (by omega)
  rcases Int.lt_or_le m (10675447966833128826886697468907 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell03 m (by omega) (by omega)
  rcases Int.lt_or_le m (10770151616997275407327261993131 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell04 m (by omega) (by omega)
  rcases Int.lt_or_le m (10914799648682411772312803110962 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell05 m (by omega) (by omega)
  rcases Int.lt_or_le m (11484527015770799509484495012553 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell06 m (by omega) (by omega)
  rcases Int.lt_or_le m (11611358934728331263016579609046 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell07 m (by omega) (by omega)
  rcases Int.lt_or_le m (12580407414500243265481207840047 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell08 m (by omega) (by omega)
  rcases Int.lt_or_le m (12790326440757707523851639277546 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltUp_cell09 m (by omega) (by omega)
  exact checkCoverK_sound _ _ _ _ _ ltUp_cell10 m (by omega) h2
end LnFloorCert
