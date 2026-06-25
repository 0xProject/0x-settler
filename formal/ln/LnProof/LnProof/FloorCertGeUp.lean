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
import LnProof.FloorCertGeUpC14

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
  refine evalPoly_ext (B := kB) certGeUp certGeUpLit ?_ ?_ ?_
  · -- Bound `polyL1 certGeUp` through the ℓ1 homomorphism lemmas applied to the
    -- (literal-coefficient) summands, then close by `exact` through the definitional
    -- equality `certGeUp ≡ polyAdd …`. Avoiding `unfold certGeUp` here is essential:
    -- the `unfold` tactic forces the kernel to reduce the degree-276 construction
    -- (minutes), whereas the defeq the final `exact` performs is lazy congruence
    -- bottoming out at `geTD ≡ geTDLit` / `geTN ≡ geTNLit` (milliseconds).
    show polyL1 certGeUp * 2 < 2 ^ kB
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
        (-(Sc : Int) * EUD).natAbs * ((23 : Int).natAbs * (LnExp.expNum 22 (polyL1 geTNLit) (polyL1 geTDLit) * polyL1 geTDLit) + (2 : Int).natAbs * polyL1 geTNLit ^ 23)) * 2 < 2 ^ kB := by
      decide +kernel
    have hA := Nat.le_trans h2 h6
    have hB := Nat.le_trans h7 h17
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 2 (Nat.le_trans h1 (Nat.add_le_add hA hB))) hfin
  · show polyL1 certGeUpLit * 2 < 2 ^ kB
    decide +kernel
  · show evalPoly certGeUp ((2 : Int) ^ kB) = evalPoly certGeUpLit ((2 : Int) ^ kB)
    rw [int_two_pow kB]
    unfold certGeUp
    rw [geTN_eq_lit, geTD_eq_lit]
    simp only [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyMul,
      evalPoly_polyPow, evalPoly_expPolyNum, eval01]
    decide +kernel

theorem geUp_nonneg {m : Int} (h1 : 56022770974786139918731938273 ≤ m) (h2 : m ≤ 79228162514264337593543950335) :
    0 ≤ evalPoly certGeUp m := by
  have hev := geUp_eval_eq m
  rw [hev]
  rcases Int.lt_or_le m (59266081817351235913474286845 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell00 m (by omega) (by omega)
  rcases Int.lt_or_le m (60261195396300777138610597146 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell01 m (by omega) (by omega)
  rcases Int.lt_or_le m (65565966845362846449121124691 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell02 m (by omega) (by omega)
  rcases Int.lt_or_le m (66268224935948723932208112262 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell03 m (by omega) (by omega)
  rcases Int.lt_or_le m (71273341474262273478494121528 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell04 m (by omega) (by omega)
  rcases Int.lt_or_le m (71949306592399438020188468464 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell05 m (by omega) (by omega)
  rcases Int.lt_or_le m (72253963783645493179901998777 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell06 m (by omega) (by omega)
  rcases Int.lt_or_le m (75848344205939394473959398558 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell07 m (by omega) (by omega)
  rcases Int.lt_or_le m (76368615273267926498199066888 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell08 m (by omega) (by omega)
  rcases Int.lt_or_le m (76512522319826533298339061377 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell09 m (by omega) (by omega)
  rcases Int.lt_or_le m (78595188666574508701639272524 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell10 m (by omega) (by omega)
  rcases Int.lt_or_le m (78835627367648889913153387938 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell11 m (by omega) (by omega)
  rcases Int.lt_or_le m (78893863486352981843045626396 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell12 m (by omega) (by omega)
  rcases Int.lt_or_le m (78941888558111820679980811876 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geUp_cell13 m (by omega) (by omega)
  exact checkCoverK_sound _ _ _ _ _ geUp_cell14 m (by omega) h2

end LnFloorCert
