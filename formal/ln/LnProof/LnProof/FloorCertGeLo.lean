import LnProof.FloorCertDefs
import LnProof.FloorCertLit
import LnProof.Kronecker
import LnProof.FloorCertGeLoC00
import LnProof.FloorCertGeLoC01
import LnProof.FloorCertGeLoC02
import LnProof.FloorCertGeLoC03
import LnProof.FloorCertGeLoC04
import LnProof.FloorCertGeLoC05
import LnProof.FloorCertGeLoC06
import LnProof.FloorCertGeLoC07
import LnProof.FloorCertGeLoC08
import LnProof.FloorCertGeLoC09
import LnProof.FloorCertGeLoC10
import LnProof.FloorCertGeLoC11
import LnProof.FloorCertGeLoC12

namespace LnFloorCert
open LnGeneratedModel LnPoly

set_option maxRecDepth 100000

theorem geTN2b_eq_lit : geTN2b = geTN2bLit := by
  unfold geTN2b geTN2 geTD2 gePLOP geDLO geAZ gePPHws geQQHwlo geA96 geWLO geD8 geB2 geA2
  decide +kernel

theorem geTD2b_eq_lit : geTD2b = geTD2bLit := by
  unfold geTD2b geTD2 geDLO geQQHwlo geWLO geD8 geB2 geA2
  decide +kernel

theorem geLo_eval_eq : ∀ x : Int, evalPoly certGeLo x = evalPoly certGeLoLit x := by
  refine evalPoly_ext (B := 50000) certGeLo certGeLoLit ?_ ?_ ?_
  · show polyL1 certGeLo * 2 < 2 ^ 50000
    unfold certGeLo
    rw [geTN2b_eq_lit, geTD2b_eq_lit]
    have h1 := polyL1_polyAdd
      (polyScale (EUD * (Sc : Int)) (expPolyNum geTN2bLit geTD2bLit 22))
      (polyScale (-(EUD - EUN) * KF) (polyMul [0, 1] (polyPow geTD2bLit 22)))
    have h2 := polyL1_polyScale (EUD * (Sc : Int)) (expPolyNum geTN2bLit geTD2bLit 22)
    have h3 := polyL1_expPolyNum geTN2bLit geTD2bLit 22
    have h7 : (EUD * (Sc : Int)).natAbs * polyL1 (expPolyNum geTN2bLit geTD2bLit 22) ≤
        (EUD * (Sc : Int)).natAbs *
          LnExp.expNum 22 (polyL1 geTN2bLit) (polyL1 geTD2bLit) :=
      Nat.mul_le_mul_left _ h3
    have h4 := polyL1_polyScale (-(EUD - EUN) * KF) (polyMul [0, 1] (polyPow geTD2bLit 22))
    have h5 := polyL1_polyMul ([0, 1] : List Int) (polyPow geTD2bLit 22)
    have h6 := polyL1_polyPow geTD2bLit 22
    have h8 : polyL1 ([0, 1] : List Int) * polyL1 (polyPow geTD2bLit 22) ≤
        polyL1 ([0, 1] : List Int) * polyL1 geTD2bLit ^ 22 :=
      Nat.mul_le_mul_left _ h6
    have h9 : (-(EUD - EUN) * KF).natAbs * polyL1 (polyMul ([0, 1] : List Int)
        (polyPow geTD2bLit 22)) ≤
        (-(EUD - EUN) * KF).natAbs *
          (polyL1 ([0, 1] : List Int) * polyL1 geTD2bLit ^ 22) :=
      Nat.mul_le_mul_left _ (Nat.le_trans h5 h8)
    have hfin : ((EUD * (Sc : Int)).natAbs *
        LnExp.expNum 22 (polyL1 geTN2bLit) (polyL1 geTD2bLit) +
        (-(EUD - EUN) * KF).natAbs *
          (polyL1 ([0, 1] : List Int) * polyL1 geTD2bLit ^ 22)) * 2 < 2 ^ 50000 := by
      decide +kernel
    generalize hgT : polyL1 (polyAdd
      (polyScale (EUD * (Sc : Int)) (expPolyNum geTN2bLit geTD2bLit 22))
      (polyScale (-(EUD - EUN) * KF) (polyMul [0, 1] (polyPow geTD2bLit 22)))) = T
      at h1 ⊢
    generalize hgA : polyL1 (polyScale (EUD * (Sc : Int))
      (expPolyNum geTN2bLit geTD2bLit 22)) = A at h1 h2
    generalize hgB : polyL1 (polyScale (-(EUD - EUN) * KF)
      (polyMul [0, 1] (polyPow geTD2bLit 22))) = B at h1 h4
    generalize hgC : (EUD * (Sc : Int)).natAbs *
      polyL1 (expPolyNum geTN2bLit geTD2bLit 22) = C at h2 h7
    generalize hgD : (EUD * (Sc : Int)).natAbs *
      LnExp.expNum 22 (polyL1 geTN2bLit) (polyL1 geTD2bLit) = D at h7 hfin
    generalize hgE : (-(EUD - EUN) * KF).natAbs * polyL1 (polyMul ([0, 1] : List Int)
      (polyPow geTD2bLit 22)) = E at h4 h9
    generalize hgF : (-(EUD - EUN) * KF).natAbs *
      (polyL1 ([0, 1] : List Int) * polyL1 geTD2bLit ^ 22) = F at h9 hfin
    omega
  · show polyL1 certGeLoLit * 2 < 2 ^ 50000
    decide +kernel
  · show evalPoly certGeLo ((2 : Int) ^ 50000) = evalPoly certGeLoLit ((2 : Int) ^ 50000)
    unfold certGeLo
    rw [geTN2b_eq_lit, geTD2b_eq_lit]
    simp only [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyMul,
      evalPoly_polyPow, evalPoly_expPolyNum, eval01]
    decide +kernel

theorem geLo_nonneg {m : Int} (h1 : 14341829369545251819195376186275 ≤ m) (h2 : m ≤ 20282409603651670423947251286015) :
    0 ≤ evalPoly certGeLo m := by
  have hev := geLo_eval_eq m
  rw [hev]
  rcases Int.lt_or_le m (15263429369545251819195376186275 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell00 m (by omega) (by omega)
  rcases Int.lt_or_le m (15678149369545251819195376186276 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell01 m (by omega) (by omega)
  rcases Int.lt_or_le m (16051397369545251819195376186277 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell02 m (by omega) (by omega)
  rcases Int.lt_or_le m (17395090169545251819195376186278 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell03 m (by omega) (by omega)
  rcases Int.lt_or_le m (17697421049545251819195376186279 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell04 m (by omega) (by omega)
  rcases Int.lt_or_le m (18241616633545251819195376186280 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell05 m (by omega) (by omega)
  rcases Int.lt_or_le m (18731392659145251819195376186281 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell06 m (by omega) (by omega)
  rcases Int.lt_or_le m (18951791870665251819195376186282 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell07 m (by omega) (by omega)
  rcases Int.lt_or_le m (19348510451401251819195376186283 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell08 m (by omega) (by omega)
  rcases Int.lt_or_le m (19705557174063651819195376186284 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell09 m (by omega) (by omega)
  rcases Int.lt_or_le m (19835348970720956005264548083723 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell10 m (by omega) (by omega)
  rcases Int.lt_or_le m (19952161587712529772726802791418 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell11 m (by omega) (by omega)
  exact checkCoverK_sound _ _ _ _ _ geLo_cell12 m (by omega) h2

end LnFloorCert
