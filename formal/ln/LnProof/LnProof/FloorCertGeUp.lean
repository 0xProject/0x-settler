import LnProof.FloorCertDefs
import LnProof.FloorCertLit
import LnProof.Kronecker
import LnProof.FloorCertGeUpC00
import LnProof.FloorCertGeUpC01
import LnProof.FloorCertGeUpC02
import LnProof.FloorCertGeUpC03
import LnProof.FloorCertGeUpC04
import LnProof.FloorCertGeUpC05
import LnProof.FloorCertGeUpC06
import LnProof.FloorCertGeUpC07
import LnProof.FloorCertGeUpC08
import LnProof.FloorCertGeUpC09
import LnProof.FloorCertGeUpC10
import LnProof.FloorCertGeUpC11
import LnProof.FloorCertGeUpC12
import LnProof.FloorCertGeUpC13

namespace LnFloorCert
open LnGeneratedModel LnPoly

set_option maxRecDepth 100000

theorem geTN_eq_lit : geTN = geTNLit := by
  unfold geTN gePPHwlo geWLO geD8 geB2 geA2
  decide +kernel

theorem geTD_eq_lit : geTD = geTDLit := by
  unfold geTD geQQHws geA96 geB2 geA2
  decide +kernel

theorem geUp_eval_eq : ∀ x : Int, evalPoly certGeUp x = evalPoly certGeUpLit x := by
  refine evalPoly_ext (B := 50000) certGeUp certGeUpLit ?_ ?_ ?_
  · show polyL1 certGeUp * 2 < 2 ^ 50000
    unfold certGeUp
    rw [geTN_eq_lit, geTD_eq_lit]
    have h1 := polyL1_polyAdd
      (polyScale ((EUD + EUN) * KF1) (polyMul [0, 1] (polyPow geTDLit 23)))
      (polyScale (-(Sc : Int) * EUD) (polyAdd (polyScale 23 (polyMul (expPolyNum geTNLit geTDLit 22) geTDLit)) (polyScale 2 (polyPow geTNLit 23))))
    have h2 := polyL1_polyScale ((EUD + EUN) * KF1) (polyMul [0, 1] (polyPow geTDLit 23))
    have h3 := polyL1_polyMul ([0, 1] : List Int) (polyPow geTDLit 23)
    have h4 := polyL1_polyPow geTDLit 23
    have h5 : polyL1 ([0, 1] : List Int) * polyL1 (polyPow geTDLit 23) ≤
        polyL1 ([0, 1] : List Int) * polyL1 geTDLit ^ 23 := Nat.mul_le_mul_left _ h4
    have h6 : ((EUD + EUN) * KF1).natAbs * polyL1 (polyMul ([0, 1] : List Int) (polyPow geTDLit 23)) ≤
        ((EUD + EUN) * KF1).natAbs * (polyL1 ([0, 1] : List Int) * polyL1 geTDLit ^ 23) :=
      Nat.mul_le_mul_left _ (Nat.le_trans h3 h5)
    have h7 := polyL1_polyScale (-(Sc : Int) * EUD) (polyAdd (polyScale 23 (polyMul (expPolyNum geTNLit geTDLit 22) geTDLit)) (polyScale 2 (polyPow geTNLit 23)))
    have h8 := polyL1_polyAdd (polyScale 23 (polyMul (expPolyNum geTNLit geTDLit 22) geTDLit)) (polyScale 2 (polyPow geTNLit 23))
    have h9 := polyL1_polyScale (23 : Int) (polyMul (expPolyNum geTNLit geTDLit 22) geTDLit)
    have h10 := polyL1_polyMul (expPolyNum geTNLit geTDLit 22) geTDLit
    have h11 := polyL1_expPolyNum geTNLit geTDLit 22
    have h12 : polyL1 (expPolyNum geTNLit geTDLit 22) * polyL1 geTDLit ≤
        LnExp.expNum 22 (polyL1 geTNLit) (polyL1 geTDLit) * polyL1 geTDLit :=
      Nat.mul_le_mul_right _ h11
    have h13 : (23 : Int).natAbs * polyL1 (polyMul (expPolyNum geTNLit geTDLit 22) geTDLit) ≤
        (23 : Int).natAbs * (LnExp.expNum 22 (polyL1 geTNLit) (polyL1 geTDLit) * polyL1 geTDLit) :=
      Nat.mul_le_mul_left _ (Nat.le_trans h10 h12)
    have h14 := polyL1_polyScale (2 : Int) (polyPow geTNLit 23)
    have h15 := polyL1_polyPow geTNLit 23
    have h16 : (2 : Int).natAbs * polyL1 (polyPow geTNLit 23) ≤
        (2 : Int).natAbs * polyL1 geTNLit ^ 23 := Nat.mul_le_mul_left _ h15
    have h17 : (-(Sc : Int) * EUD).natAbs * polyL1 (polyAdd (polyScale 23 (polyMul (expPolyNum geTNLit geTDLit 22) geTDLit)) (polyScale 2 (polyPow geTNLit 23))) ≤
        (-(Sc : Int) * EUD).natAbs * ((23 : Int).natAbs * (LnExp.expNum 22 (polyL1 geTNLit) (polyL1 geTDLit) * polyL1 geTDLit) + (2 : Int).natAbs * polyL1 geTNLit ^ 23) := by
      refine Nat.mul_le_mul_left _ ?_
      have := Nat.le_trans h9 h13
      have h14' := Nat.le_trans h14 h16
      omega
    have hfin : (((EUD + EUN) * KF1).natAbs * (polyL1 ([0, 1] : List Int) * polyL1 geTDLit ^ 23) +
        (-(Sc : Int) * EUD).natAbs * ((23 : Int).natAbs * (LnExp.expNum 22 (polyL1 geTNLit) (polyL1 geTDLit) * polyL1 geTDLit) + (2 : Int).natAbs * polyL1 geTNLit ^ 23)) * 2 < 2 ^ 50000 := by
      decide +kernel
    have hA := Nat.le_trans h2 h6
    have hB := Nat.le_trans h7 h17
    omega
  · show polyL1 certGeUpLit * 2 < 2 ^ 50000
    decide +kernel
  · show evalPoly certGeUp ((2 : Int) ^ 50000) = evalPoly certGeUpLit ((2 : Int) ^ 50000)
    unfold certGeUp
    rw [geTN_eq_lit, geTD_eq_lit]
    simp only [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyMul,
      evalPoly_polyPow, evalPoly_expPolyNum, eval01]
    decide +kernel

theorem geUp_nonneg {m : Int} (h1 : 14341829369545251819195376186275 ≤ m) (h2 : m ≤ 20282409603651670423947251286015) :
    0 ≤ evalPoly certGeUp m := by
  have hev := geUp_eval_eq m
  rw [hev]
  rcases Int.lt_or_le m (14802629369545251819195376186275 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell00 m (by omega) (by omega)
  rcases Int.lt_or_le m (15632069369545251819195376186276 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell01 m (by omega) (by omega)
  rcases Int.lt_or_le m (16378565369545251819195376186277 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell02 m (by omega) (by omega)
  rcases Int.lt_or_le m (16714488569545251819195376186278 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell03 m (by omega) (by omega)
  rcases Int.lt_or_le m (17319150329545251819195376186279 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell04 m (by omega) (by omega)
  rcases Int.lt_or_le m (17863345913545251819195376186280 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell05 m (by omega) (by omega)
  rcases Int.lt_or_le m (18353121939145251819195376186281 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell06 m (by omega) (by omega)
  rcases Int.lt_or_le m (19234718785225251819195376186282 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell07 m (by omega) (by omega)
  rcases Int.lt_or_le m (19470449219371196005264548083722 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell08 m (by omega) (by omega)
  rcases Int.lt_or_le m (19682606610102545772726802791418 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell09 m (by omega) (by omega)
  rcases Int.lt_or_le m (20064489913418975354158861265270 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell10 m (by omega) (by omega)
  rcases Int.lt_or_le m (20162553774023688135563636774605 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell11 m (by omega) (by omega)
  rcases Int.lt_or_le m (20216488897356280165336263304739 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell12 m (by omega) (by omega)
  exact checkCoverK_sound _ _ _ _ _ geUp_cell13 m (by omega) h2

end LnFloorCert
