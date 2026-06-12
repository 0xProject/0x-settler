import LnProof.FloorCaps
import LnProof.FloorBudget
import LnProof.FloorConsts
import LnProof.FloorCertGeUp
import LnProof.FloorCertGeLo
import LnProof.FloorCertLtUp
import LnProof.FloorCertLtLo

/-!
# Full-branch X1 caps

The certificate rationals only bracket the pipeline outside the
`|m - S| ≤ 45` window, where the certified ε keeps its margin. Inside
the window the pipeline argument is within a few parts in `10^30` of
zero, so the caps hold pointwise with room to spare; they are checked
here by kernel evaluation of the partial-sum conditions at each of the
91 mantissas, and combined with the certificate route into caps that
cover each whole branch.
-/

namespace LnFloorCert
open LnGeneratedModel LnPoly LnExp LnFloor

set_option maxRecDepth 10000

/-- Pointwise window check, `m = Sc + i`, `0 ≤ i ≤ 45`. -/
def wCheckGe (i : Nat) : Bool :=
  decide (0 ≤ toInt (x1W (zWord (Sc + i)))) &&
  decide (2 * ((toInt (x1W (zWord (Sc + i)))).toNat * 1000000000000000000000000000) ≤
    24 * QS) &&
  decide ((expNum 22 ((toInt (x1W (zWord (Sc + i)))).toNat *
      1000000000000000000000000000) QS * (23 * QS) +
      2 * ((toInt (x1W (zWord (Sc + i)))).toNat * 1000000000000000000000000000) ^ 23) *
      1434182936954525181919537618622900000000000000000000000000000 ≤
    (Sc + i) * 100000000000000000000000000042 * (fact 23 * QS ^ 23)) &&
  decide ((Sc + i) * 99999999999999999999999999958 * (fact 22 * QS ^ 22) ≤
    expNum 22 ((toInt (x1W (zWord (Sc + i)))).toNat * 1000000000000000000000000000) QS *
      1434182936954525181919537618622900000000000000000000000000000)

/-- Pointwise window check, `m = Sc - 45 + i`, `0 ≤ i ≤ 44`. -/
def wCheckLt (i : Nat) : Bool :=
  decide (toInt (x1W (zWord (Sc - 45 + i))) ≤ 0) &&
  decide (2 * ((-toInt (x1W (zWord (Sc - 45 + i)))).toNat *
    1000000000000000000000000000) ≤ 24 * QS) &&
  decide ((expNum 22 ((-toInt (x1W (zWord (Sc - 45 + i)))).toNat *
      1000000000000000000000000000) QS * (23 * QS) +
      2 * ((-toInt (x1W (zWord (Sc - 45 + i)))).toNat *
        1000000000000000000000000000) ^ 23) *
      ((Sc - 45 + i) * 99999999999999999999999999958) ≤
    1434182936954525181919537618622900000000000000000000000000000 *
      (fact 23 * QS ^ 23)) &&
  decide (1434182936954525181919537618622900000000000000000000000000000 *
      (fact 22 * QS ^ 22) ≤
    expNum 22 ((-toInt (x1W (zWord (Sc - 45 + i)))).toNat *
      1000000000000000000000000000) QS *
      ((Sc - 45 + i) * 100000000000000000000000000042))

theorem wCheckGe_all : (List.range 46).all wCheckGe = true := by
  decide +kernel

theorem wCheckLt_all : (List.range 45).all wCheckLt = true := by
  decide +kernel

theorem wGe_facts {m : Nat} (h1 : Sc ≤ m) (h2 : m ≤ Sc + 45) :
    0 ≤ toInt (x1W (zWord m)) ∧
    capUB ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000) QS
      (m * 100000000000000000000000000042)
      1434182936954525181919537618622900000000000000000000000000000 ∧
    capLB ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000) QS
      (m * 99999999999999999999999999958)
      1434182936954525181919537618622900000000000000000000000000000 := by
  have hi := List.all_eq_true.mp wCheckGe_all (m - Sc) (List.mem_range.mpr (by omega))
  simp only [wCheckGe, Bool.and_eq_true, decide_eq_true_eq] at hi
  rw [show Sc + (m - Sc) = m from by omega] at hi
  obtain ⟨⟨⟨hsign, hH⟩, hUB⟩, hLB⟩ := hi
  refine ⟨hsign, ?_, ⟨22, hLB⟩⟩
  exact capUB_of_partial QS_pos hH hUB

theorem wLt_facts {m : Nat} (h1 : Sc - 45 ≤ m) (h2 : m < Sc) :
    toInt (x1W (zWord m)) ≤ 0 ∧
    capLB ((-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000) QS
      1434182936954525181919537618622900000000000000000000000000000
      (m * 100000000000000000000000000042) ∧
    capUB ((-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000) QS
      1434182936954525181919537618622900000000000000000000000000000
      (m * 99999999999999999999999999958) := by
  have hi := List.all_eq_true.mp wCheckLt_all (m - (Sc - 45))
    (List.mem_range.mpr (by simp only [Sc] at h1 h2 ⊢; omega))
  simp only [wCheckLt, Bool.and_eq_true, decide_eq_true_eq] at hi
  rw [show Sc - 45 + (m - (Sc - 45)) = m from by simp only [Sc] at h1 ⊢; omega] at hi
  obtain ⟨⟨⟨hsign, hH⟩, hUB⟩, hLB⟩ := hi
  refine ⟨hsign, ⟨22, hLB⟩, ?_⟩
  exact capUB_of_partial QS_pos hH hUB

/-! ## Full-branch caps and signs -/

theorem x1_nonneg_geF {m : Nat} (h1 : Sc ≤ m) (h2 : m < MHI) :
    0 ≤ toInt (x1W (zWord m)) := by
  rcases Nat.lt_or_ge m (Sc + 46) with hw | ho
  · exact (wGe_facts h1 (by omega)).1
  · exact x1_nonneg_ge ho h2

theorem x1_nonpos_ltF {m : Nat} (h1 : MLO ≤ m) (h2 : m < Sc) :
    toInt (x1W (zWord m)) ≤ 0 := by
  rcases Nat.lt_or_ge m (Sc - 45) with ho | hw
  · exact x1_nonpos_lt h1 (by simp only [Sc] at ho ⊢; omega)
  · exact (wLt_facts hw h2).1

theorem x1capGeUpF {m : Nat} (h1 : Sc ≤ m) (h2 : m < MHI) :
    capUB ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000) QS
      (m * 100000000000000000000000000042)
      1434182936954525181919537618622900000000000000000000000000000 := by
  rcases Nat.lt_or_ge m (Sc + 46) with hw | ho
  · exact (wGe_facts h1 (by omega)).2.1
  · have hup := geUp_nonneg (m := (m : Int))
      (by simp only [Sc] at ho; omega) (by simp only [MHI] at h2; omega)
    have h := x1capGeUp ho h2 hup
    rw [show (633825300114114700748351602688000000000000000000000000000 : Nat) = QS
      from by decide] at h
    exact h

theorem x1capGeLoF {m : Nat} (h1 : Sc ≤ m) (h2 : m < MHI) :
    capLB ((toInt (x1W (zWord m))).toNat * 1000000000000000000000000000) QS
      (m * 99999999999999999999999999958)
      1434182936954525181919537618622900000000000000000000000000000 := by
  rcases Nat.lt_or_ge m (Sc + 46) with hw | ho
  · exact (wGe_facts h1 (by omega)).2.2
  · have hlo := geLo_nonneg (m := (m : Int))
      (by simp only [Sc] at ho; omega) (by simp only [MHI] at h2; omega)
    have h := x1capGeLo ho h2 hlo
    rw [show (633825300114114700748351602688000000000000000000000000000 : Nat) = QS
      from by decide] at h
    exact h

theorem x1capLtUpF {m : Nat} (h1 : MLO ≤ m) (h2 : m < Sc) :
    capLB ((-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000) QS
      1434182936954525181919537618622900000000000000000000000000000
      (m * 100000000000000000000000000042) := by
  rcases Nat.lt_or_ge m (Sc - 45) with ho | hw
  · have hup := ltUp_nonneg (m := (m : Int))
      (by simp only [MLO] at h1; omega) (by simp only [Sc] at ho ⊢; omega)
    have h := x1capLtUp h1 (by simp only [Sc] at ho ⊢; omega) hup
    rw [show (633825300114114700748351602688000000000000000000000000000 : Nat) = QS
      from by decide] at h
    exact h
  · exact (wLt_facts hw h2).2.1

theorem x1capLtLoF {m : Nat} (h1 : MLO ≤ m) (h2 : m < Sc) :
    capUB ((-toInt (x1W (zWord m))).toNat * 1000000000000000000000000000) QS
      1434182936954525181919537618622900000000000000000000000000000
      (m * 99999999999999999999999999958) := by
  rcases Nat.lt_or_ge m (Sc - 45) with ho | hw
  · have hlo := ltLo_nonneg (m := (m : Int))
      (by simp only [MLO] at h1; omega) (by simp only [Sc] at ho ⊢; omega)
    have h := x1capLtLo h1 (by simp only [Sc] at ho ⊢; omega) hlo
    rw [show (633825300114114700748351602688000000000000000000000000000 : Nat) = QS
      from by decide] at h
    exact h
  · exact (wLt_facts hw h2).2.2

end LnFloorCert
