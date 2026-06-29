import LnProof.Floor.CertDefs
import LnProof.Cert.FloorCertLit
import Common.Foundation.Kronecker
import LnProof.Cert.FloorCertLtLoC00
import LnProof.Cert.FloorCertLtLoC01
import LnProof.Cert.FloorCertLtLoC02
import LnProof.Cert.FloorCertLtLoC03
import LnProof.Cert.FloorCertLtLoC04
import LnProof.Cert.FloorCertLtLoC05
import LnProof.Cert.FloorCertLtLoC06
import LnProof.Cert.FloorCertLtLoC07
import LnProof.Cert.FloorCertLtLoC08
import LnProof.Cert.FloorCertLtLoC09
import LnProof.Cert.FloorCertLtLoC10
import LnProof.Cert.FloorCertLtLoC11
import LnProof.Cert.FloorCertLtLoC12
import LnProof.Cert.FloorCertLtLoC13
import LnProof.Cert.FloorCertLtLoC14
import LnProof.Cert.FloorCertLtLoC15

namespace LnFloorCert
open LnYul Common.Poly

set_option maxRecDepth 100000

theorem ltTN_eq_lit : ltTN = ltTNLit := by
  unfold ltTN ltPPHwlo ltWLO ltD8 ltB2 ltA2
  decide +kernel

theorem ltTD_eq_lit : ltTD = ltTDLit := by
  unfold ltTD ltQQHws ltA96 ltB2 ltA2
  decide +kernel

theorem ltLo_eval_eq : ∀ x : Int, evalPoly certLtLo x = evalPoly certLtLoLit x := by
  refine evalPoly_ext (B := kB) certLtLo certLtLoLit ?_ ?_ ?_
  · -- Bound `polyL1 certLtLo` via the ℓ1 homomorphism lemmas on the literal
    -- summands, closing by `exact` through the definitional equality
    -- `certLtLo ≡ polyAdd …`. `unfold certLtLo` is avoided: it forces the kernel
    -- to reduce the full construction (minutes); the `exact` defeq is lazy
    -- congruence bottoming out at `ltTD ≡ ltTDLit` (milliseconds).
    show polyL1 certLtLo * 2 < 2 ^ kB
    have h1 := polyL1_polyAdd
      (polyScale ((Sc : Int) * EUD * KF1) (polyPow ltTDLit 23))
      (polyScale (-(EUD - EUNl)) (polyMul [0, 1] (polyAdd (polyScale 23 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit)) (polyScale 2 (polyPow ltTNLit 23)))))
    have h2 := polyL1_polyScale ((Sc : Int) * EUD * KF1) (polyPow ltTDLit 23)
    have h3 := polyL1_polyPow ltTDLit 23
    have h4 : ((Sc : Int) * EUD * KF1).natAbs * polyL1 (polyPow ltTDLit 23) ≤
        ((Sc : Int) * EUD * KF1).natAbs * polyL1 ltTDLit ^ 23 :=
      Nat.mul_le_mul_left _ h3
    have h5 := polyL1_polyScale (-(EUD - EUNl)) (polyMul [0, 1] (polyAdd (polyScale 23 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit)) (polyScale 2 (polyPow ltTNLit 23))))
    have h6 := polyL1_polyMul ([0, 1] : List Int) (polyAdd (polyScale 23 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit)) (polyScale 2 (polyPow ltTNLit 23)))
    have h7 := polyL1_polyAdd (polyScale 23 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit)) (polyScale 2 (polyPow ltTNLit 23))
    have h8 := polyL1_polyScale (23 : Int) (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit)
    have h9 := polyL1_polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit
    have h10 := polyL1_expPolyNum ltTNLit ltTDLit 22
    have h11 : polyL1 (expPolyNum ltTNLit ltTDLit 22) * polyL1 ltTDLit ≤
        Common.Exp.expNum 22 (polyL1 ltTNLit) (polyL1 ltTDLit) * polyL1 ltTDLit :=
      Nat.mul_le_mul_right _ h10
    have h12 : (23 : Int).natAbs * polyL1 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit) ≤
        (23 : Int).natAbs * (Common.Exp.expNum 22 (polyL1 ltTNLit) (polyL1 ltTDLit) * polyL1 ltTDLit) :=
      Nat.mul_le_mul_left _ (Nat.le_trans h9 h11)
    have h13 := polyL1_polyScale (2 : Int) (polyPow ltTNLit 23)
    have h14 := polyL1_polyPow ltTNLit 23
    have h15 : (2 : Int).natAbs * polyL1 (polyPow ltTNLit 23) ≤
        (2 : Int).natAbs * polyL1 ltTNLit ^ 23 := Nat.mul_le_mul_left _ h14
    have h16 : polyL1 ([0, 1] : List Int) * polyL1 (polyAdd (polyScale 23 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit)) (polyScale 2 (polyPow ltTNLit 23))) ≤
        polyL1 ([0, 1] : List Int) * ((23 : Int).natAbs * (Common.Exp.expNum 22 (polyL1 ltTNLit) (polyL1 ltTDLit) * polyL1 ltTDLit) + (2 : Int).natAbs * polyL1 ltTNLit ^ 23) := by
      refine Nat.mul_le_mul_left _ ?_
      have hx := Nat.le_trans h8 h12
      have hy := Nat.le_trans h13 h15
      omega
    have h17 : (-(EUD - EUNl)).natAbs * polyL1 (polyMul ([0, 1] : List Int) (polyAdd (polyScale 23 (polyMul (expPolyNum ltTNLit ltTDLit 22) ltTDLit)) (polyScale 2 (polyPow ltTNLit 23)))) ≤
        (-(EUD - EUNl)).natAbs * (polyL1 ([0, 1] : List Int) * ((23 : Int).natAbs * (Common.Exp.expNum 22 (polyL1 ltTNLit) (polyL1 ltTDLit) * polyL1 ltTDLit) + (2 : Int).natAbs * polyL1 ltTNLit ^ 23)) :=
      Nat.mul_le_mul_left _ (Nat.le_trans h6 h16)
    have hfin : (((Sc : Int) * EUD * KF1).natAbs * polyL1 ltTDLit ^ 23 +
        (-(EUD - EUNl)).natAbs * (polyL1 ([0, 1] : List Int) * ((23 : Int).natAbs * (Common.Exp.expNum 22 (polyL1 ltTNLit) (polyL1 ltTDLit) * polyL1 ltTDLit) + (2 : Int).natAbs * polyL1 ltTNLit ^ 23))) * 2 < 2 ^ kB := by
      decide +kernel
    have hA := Nat.le_trans h2 h4
    have hB := Nat.le_trans h5 h17
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 2 (Nat.le_trans h1 (Nat.add_le_add hA hB))) hfin
  · show polyL1 certLtLoLit * 2 < 2 ^ kB
    decide +kernel
  · show evalPoly certLtLo ((2 : Int) ^ kB) = evalPoly certLtLoLit ((2 : Int) ^ kB)
    rw [int_two_pow kB]
    unfold certLtLo
    rw [ltTN_eq_lit, ltTD_eq_lit]
    simp only [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyMul,
      evalPoly_polyPow, evalPoly_expPolyNum, eval01]
    decide +kernel

theorem ltLo_nonneg {m : Int} (h1 : 39614081257132168796771975168 ≤ m) (h2 : m ≤ 56022770974786139918731938181) :
    0 ≤ evalPoly certLtLo m := by
  have hev := ltLo_eval_eq m
  rw [hev]
  rcases Int.lt_or_le m (39691340757316876069324712922 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell00 m (by omega) (by omega)
  rcases Int.lt_or_le m (39732444922577553617482767860 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell01 m (by omega) (by omega)
  rcases Int.lt_or_le m (39756001564454929649831775393 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell02 m (by omega) (by omega)
  rcases Int.lt_or_le m (39775810836879769148708517055 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell03 m (by omega) (by omega)
  rcases Int.lt_or_le m (40681837264845746378138783533 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell04 m (by omega) (by omega)
  rcases Int.lt_or_le m (40930227933353587876109008873 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell05 m (by omega) (by omega)
  rcases Int.lt_or_le m (41011130847228556948232053376 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell06 m (by omega) (by omega)
  rcases Int.lt_or_le m (41193980475986553311038374013 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell07 m (by omega) (by omega)
  rcases Int.lt_or_le m (43109808225948037345826844487 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell08 m (by omega) (by omega)
  rcases Int.lt_or_le m (43461196674852073537873737449 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell09 m (by omega) (by omega)
  rcases Int.lt_or_le m (43629975768989603972780827922 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell10 m (by omega) (by omega)
  rcases Int.lt_or_le m (46784481610765814240449867875 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell11 m (by omega) (by omega)
  rcases Int.lt_or_le m (47282531113563457243010691206 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell12 m (by omega) (by omega)
  rcases Int.lt_or_le m (51672663982950937922364563652 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell13 m (by omega) (by omega)
  rcases Int.lt_or_le m (52579881301127525176107597773 + 1) with h | h
  · exact checkCoverK_sound _ _ _ _ _ ltLo_cell14 m (by omega) (by omega)
  exact checkCoverK_sound _ _ _ _ _ ltLo_cell15 m (by omega) h2

end LnFloorCert
