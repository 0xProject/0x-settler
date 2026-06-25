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
import LnProof.FloorCertGeLoC13

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
          LnExp.expNum 22 (polyL1 geTN2bLit) (polyL1 geTD2bLit) :=
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
        LnExp.expNum 22 (polyL1 geTN2bLit) (polyL1 geTD2bLit) +
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

theorem geLo_nonneg {m : Int} (h1 : 56022770974786139918731938273 ≤ m) (h2 : m ≤ 79228162514264337593543950335) :
    0 ≤ evalPoly certGeLo m := by
  have hev := geLo_eval_eq m
  rw [hev]
  rcases Int.lt_or_le m (62248863508307989581262617183 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell00 m (by omega) (by omega)
  rcases Int.lt_or_le m (63042232383408656869457414737 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell01 m (by omega) (by omega)
  rcases Int.lt_or_le m (64929052012891719377728977367 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell02 m (by omega) (by omega)
  rcases Int.lt_or_le m (68717504609657537844941640470 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell03 m (by omega) (by omega)
  rcases Int.lt_or_le m (69233132140651152842861403916 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell04 m (by omega) (by omega)
  rcases Int.lt_or_le m (69643680272268497720544738509 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell05 m (by omega) (by omega)
  rcases Int.lt_or_le m (73761687789119228727691347873 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell06 m (by omega) (by omega)
  rcases Int.lt_or_le m (74347359659513480232328600324 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell07 m (by omega) (by omega)
  rcases Int.lt_or_le m (74497159690857676763262189492 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell08 m (by omega) (by omega)
  rcases Int.lt_or_le m (77437517811705333581000648120 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell09 m (by omega) (by omega)
  rcases Int.lt_or_le m (77857333859755213679737086192 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell10 m (by omega) (by omega)
  rcases Int.lt_or_le m (77947664376793543259244624794 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell11 m (by omega) (by omega)
  rcases Int.lt_or_le m (78001071025949577278638182916 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ geLo_cell12 m (by omega) (by omega)
  exact checkCoverK_sound _ _ _ _ _ geLo_cell13 m (by omega) h2
end LnFloorCert
