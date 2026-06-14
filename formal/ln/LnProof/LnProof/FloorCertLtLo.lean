import LnProof.FloorCertDefs
import LnProof.FloorCertLit
import LnProof.Kronecker
import LnProof.FloorCertLtLoC00
import LnProof.FloorCertLtLoC01
import LnProof.FloorCertLtLoC02
import LnProof.FloorCertLtLoC03
import LnProof.FloorCertLtLoC04
import LnProof.FloorCertLtLoC05
import LnProof.FloorCertLtLoC06
import LnProof.FloorCertLtLoC07
import LnProof.FloorCertLtLoC08
import LnProof.FloorCertLtLoC09
import LnProof.FloorCertLtLoC10
import LnProof.FloorCertLtLoC11
import LnProof.FloorCertLtLoC12

namespace LnFloorCert
open LnGeneratedModel LnPoly

set_option maxRecDepth 100000

theorem ltTN_eq_lit : ltTN = ltTNLit := by
  unfold ltTN ltPPHwlo ltWLO ltD8 ltB2 ltA2
  decide +kernel

theorem ltTD_eq_lit : ltTD = ltTDLit := by
  unfold ltTD ltQQHws ltA96 ltB2 ltA2
  decide +kernel

theorem ltLo_eval_eq : ∀ x : Int, evalPoly certLtLo x = evalPoly certLtLoLit x := by
  refine evalPoly_ext (B := 38000) certLtLo certLtLoLit ?_ ?_ ?_
  · show polyL1 certLtLo * 2 < 2 ^ 38000
    unfold certLtLo
    rw [ltTN_eq_lit, ltTD_eq_lit]
    have h1 := polyL1_polyAdd
      (polyScale ((Sc : Int) * EUD * KF1) (polyPow ltTDLit 23))
      (polyScale (-(EUD - EUN)) (polyMul [0, 1] (polyAdd (polyScale 23 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit)) (polyScale 2 (polyPow ltTNLit 23)))))
    have h2 := polyL1_polyScale ((Sc : Int) * EUD * KF1) (polyPow ltTDLit 23)
    have h3 := polyL1_polyPow ltTDLit 23
    have h4 : ((Sc : Int) * EUD * KF1).natAbs * polyL1 (polyPow ltTDLit 23) ≤
        ((Sc : Int) * EUD * KF1).natAbs * polyL1 ltTDLit ^ 23 :=
      Nat.mul_le_mul_left _ h3
    have h5 := polyL1_polyScale (-(EUD - EUN)) (polyMul [0, 1] (polyAdd (polyScale 23 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit)) (polyScale 2 (polyPow ltTNLit 23))))
    have h6 := polyL1_polyMul ([0, 1] : List Int) (polyAdd (polyScale 23 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit)) (polyScale 2 (polyPow ltTNLit 23)))
    have h7 := polyL1_polyAdd (polyScale 23 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit)) (polyScale 2 (polyPow ltTNLit 23))
    have h8 := polyL1_polyScale (23 : Int) (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit)
    have h9 := polyL1_polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit
    have h10 := polyL1_expPolyNum ltTNLit ltTDLit 22
    have h11 : polyL1 (expPolyNum ltTNLit ltTDLit 22) * polyL1 ltTDLit ≤
        LnExp.expNum 22 (polyL1 ltTNLit) (polyL1 ltTDLit) * polyL1 ltTDLit :=
      Nat.mul_le_mul_right _ h10
    have h12 : (23 : Int).natAbs * polyL1 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit) ≤
        (23 : Int).natAbs * (LnExp.expNum 22 (polyL1 ltTNLit) (polyL1 ltTDLit) * polyL1 ltTDLit) :=
      Nat.mul_le_mul_left _ (Nat.le_trans h9 h11)
    have h13 := polyL1_polyScale (2 : Int) (polyPow ltTNLit 23)
    have h14 := polyL1_polyPow ltTNLit 23
    have h15 : (2 : Int).natAbs * polyL1 (polyPow ltTNLit 23) ≤
        (2 : Int).natAbs * polyL1 ltTNLit ^ 23 := Nat.mul_le_mul_left _ h14
    have h16 : polyL1 ([0, 1] : List Int) * polyL1 (polyAdd (polyScale 23 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit)) (polyScale 2 (polyPow ltTNLit 23))) ≤
        polyL1 ([0, 1] : List Int) * ((23 : Int).natAbs * (LnExp.expNum 22 (polyL1 ltTNLit) (polyL1 ltTDLit) * polyL1 ltTDLit) + (2 : Int).natAbs * polyL1 ltTNLit ^ 23) := by
      refine Nat.mul_le_mul_left _ ?_
      have hx := Nat.le_trans h8 h12
      have hy := Nat.le_trans h13 h15
      omega
    have h17 : (-(EUD - EUN)).natAbs * polyL1 (polyMul ([0, 1] : List Int) (polyAdd (polyScale 23 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit)) (polyScale 2 (polyPow ltTNLit 23)))) ≤
        (-(EUD - EUN)).natAbs * (polyL1 ([0, 1] : List Int) * ((23 : Int).natAbs * (LnExp.expNum 22 (polyL1 ltTNLit) (polyL1 ltTDLit) * polyL1 ltTDLit) + (2 : Int).natAbs * polyL1 ltTNLit ^ 23)) :=
      Nat.mul_le_mul_left _ (Nat.le_trans h6 h16)
    have hfin : (((Sc : Int) * EUD * KF1).natAbs * polyL1 ltTDLit ^ 23 +
        (-(EUD - EUN)).natAbs * (polyL1 ([0, 1] : List Int) * ((23 : Int).natAbs * (LnExp.expNum 22 (polyL1 ltTNLit) (polyL1 ltTDLit) * polyL1 ltTDLit) + (2 : Int).natAbs * polyL1 ltTNLit ^ 23))) * 2 < 2 ^ 38000 := by
      decide +kernel
    have hA := Nat.le_trans h2 h4
    have hB := Nat.le_trans h5 h17
    omega
  · show polyL1 certLtLoLit * 2 < 2 ^ 38000
    decide +kernel
  · show evalPoly certLtLo ((2 : Int) ^ 38000) = evalPoly certLtLoLit ((2 : Int) ^ 38000)
    unfold certLtLo
    rw [ltTN_eq_lit, ltTD_eq_lit]
    simp only [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyMul,
      evalPoly_polyPow, evalPoly_expPolyNum, eval01]
    decide +kernel

theorem ltLo_nonneg {m : Int} (h1 : 10141204801825835211973625643008 ≤ m) (h2 : m ≤ 14341829369545251819195376186183) :
    0 ≤ evalPoly certLtLo m := by
  have hev := ltLo_eval_eq m
  rw [hev]
  rcases Int.lt_or_le m (10155604801825835211973625643008 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell00 m (by omega) (by omega)
  rcases Int.lt_or_le m (10168564801825835211973625643009 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell01 m (by omega) (by omega)
  rcases Int.lt_or_le m (10180228801825835211973625643010 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell02 m (by omega) (by omega)
  rcases Int.lt_or_le m (10348190401825835211973625643011 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell03 m (by omega) (by omega)
  rcases Int.lt_or_le m (10423773121825835211973625643012 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell04 m (by omega) (by omega)
  rcases Int.lt_or_le m (10491797569825835211973625643013 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell05 m (by omega) (by omega)
  rcases Int.lt_or_le m (10981573595425835211973625643014 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell06 m (by omega) (by omega)
  rcases Int.lt_or_le m (11091773201185835211973625643015 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell07 m (by omega) (by omega)
  rcases Int.lt_or_le m (11885210362657835211973625643016 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell08 m (by omega) (by omega)
  rcases Int.lt_or_le m (12242257085320235211973625643017 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell09 m (by omega) (by omega)
  rcases Int.lt_or_le m (12884941186112555211973625643018 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell10 m (by omega) (by omega)
  rcases Int.lt_or_le m (13463356876825643211973625643019 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell11 m (by omega) (by omega)
  exact checkCoverK_sound _ _ _ _ _ ltLo_cell12 m (by omega) h2

end LnFloorCert
