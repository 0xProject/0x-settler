import LnProof.Floor.CutEquiv
import LnProof.Error.Cert
import LnProof.Error.Core.CutDefs
import LnProof.Error.Core.ExpMargin
import LnProof.Error.Core.Budget

/-!
# Error bound — PhaseGe

Ge-branch phase-lower margin polynomials and their soundness.
-/

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

namespace LnFloorCert

open LnYul LnFloor Common.Exp Common.Poly

attribute [local irreducible] lnWadToRayBody


def posTopXPoly (c : Nat) : List Int :=
  [((2 ^ (160 - c) : Nat) : Int) - 1, ((2 ^ (160 - c) : Nat) : Int)]

theorem eval_posTopXPoly (m c : Nat) :
    evalPoly (posTopXPoly c) (m : Int) = (posTopX c m : Int) := by
  unfold posTopXPoly posTopX
  simp only [evalPoly]
  have hpow : 0 < 2 ^ (160 - c) := Nat.pow_pos (by decide)
  have hprod : 1 ≤ (m + 1) * 2 ^ (160 - c) := Nat.succ_le_of_lt
    (Nat.mul_pos (Nat.succ_pos m) hpow)
  rw [Int.natCast_sub (n := 1) (m := (m + 1) * 2 ^ (160 - c)) hprod]
  simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_one, Int.mul_zero, Int.add_zero]
  rw [Int.add_mul, Int.one_mul]
  omega

def gePhaseLowerPN (c : Nat) : List Int :=
  polyAdd
    (polyScale (((2 ^ 99 * lnPhaseScaleN * lnErrorBoundDen : Nat) : Int)) geTN2b)
    (polyScale (((posConstNat c + lnPhaseExtraArg : Nat) : Int)) geTD2b)

def gePhaseLowerQD : List Int :=
  polyScale ((lnErrQ : Nat) : Int) geTD2b

def gePhaseLowerMarginPoly (c : Nat) : List Int :=
  expMarginPolyFast 320 (gePhaseLowerPN c) gePhaseLowerQD (posTopXPoly c) (10 ^ 18)

theorem geTD2b_pos_of_outer {m : Nat} (h1 : Sc + 46 ≤ m) (h2 : m < MHI) :
    0 < evalPoly geTD2b (m : Int) := by
  have hw1 : (56022770974786139918731938273 : Int) ≤ (m : Int) := by
    simp only [Sc] at h1
    omega
  have hw2 : (m : Int) ≤ 79228162514264337593543950335 := by
    simp only [MHI] at h2
    omega
  have h := geTD2_nonneg hw1 hw2
  rw [evalCertGeTD2] at h
  omega

theorem geTN2b_nonneg_of_outer {m : Nat} (h1 : Sc + 46 ≤ m) (h2 : m < MHI) :
    0 ≤ evalPoly geTN2b (m : Int) := by
  have hw1 : (56022770974786139918731938273 : Int) ≤ (m : Int) := by
    simp only [Sc] at h1
    omega
  have hw2 : (m : Int) ≤ 79228162514264337593543950335 := by
    simp only [MHI] at h2
    omega
  exact geTN2_nonneg hw1 hw2

theorem gePhaseLowerPN_nonneg {m c : Nat} (h1 : Sc + 46 ≤ m) (h2 : m < MHI) :
    0 ≤ evalPoly (gePhaseLowerPN c) (m : Int) := by
  have htn := geTN2b_nonneg_of_outer h1 h2
  have htd : 0 ≤ evalPoly geTD2b (m : Int) := by
    exact Int.le_of_lt (geTD2b_pos_of_outer h1 h2)
  unfold gePhaseLowerPN
  rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyScale]
  exact Int.add_nonneg
    (Int.mul_nonneg (Int.natCast_nonneg _) htn)
    (Int.mul_nonneg (Int.natCast_nonneg _) htd)

theorem gePhaseLowerQD_pos {m : Nat} (h1 : Sc + 46 ≤ m) (h2 : m < MHI) :
    0 < evalPoly gePhaseLowerQD (m : Int) := by
  unfold gePhaseLowerQD
  rw [evalPoly_polyScale]
  exact Int.mul_pos (by unfold lnErrQ QS lnErrorBoundDen; decide)
    (geTD2b_pos_of_outer h1 h2)

theorem posPhaseNatGe_cast_decomp {m c : Nat}
    (hX : 0 ≤ int256 (x1W (zWord m))) :
    ((posPhaseNatGe m c : Nat) : Int) =
      int256 (x1W (zWord m)) *
        ((lnPhaseScaleN * lnErrorBoundDen : Nat) : Int) +
          (posConstNat c : Int) := by
  have hXn : (((int256 (x1W (zWord m))).toNat : Nat) : Int) =
      int256 (x1W (zWord m)) :=
    Int.toNat_of_nonneg hX
  unfold posPhaseNatGe posConstNat
  simp only [Int.natCast_add, Int.natCast_mul, hXn]
  simp only [Int.mul_assoc]
  rw [Int.add_assoc]

theorem gePhaseLowerPN_le_phase_mul_TD {m c : Nat}
    (h1 : Sc + 46 ≤ m) (h2 : m < MHI) :
    evalPoly (gePhaseLowerPN c) (m : Int) ≤
      ((posPhaseNatGe m c + lnPhaseExtraArg : Nat) : Int) *
        evalPoly geTD2b (m : Int) := by
  have hbr := bracket_ge_lo h1 h2
  generalize hTN : evalPoly geTN2b (m : Int) = TN at hbr ⊢
  generalize hTD : evalPoly geTD2b (m : Int) = TD at hbr ⊢
  have hX := x1_nonneg_ge h1 h2
  have hphase0 := posPhaseNatGe_cast_decomp (m := m) (c := c) hX
  generalize hXV : int256 (x1W (zWord m)) = X at hbr hphase0 ⊢
  let K : Int := ((lnPhaseScaleN * lnErrorBoundDen : Nat) : Int)
  let C : Int := (posConstNat c : Int)
  let E : Int := (lnPhaseExtraArg : Int)
  have hphase :
      ((posPhaseNatGe m c + lnPhaseExtraArg : Nat) : Int) = X * K + C + E := by
    rw [Int.natCast_add, hphase0]
  have hpn :
      evalPoly (gePhaseLowerPN c) (m : Int) = (2 ^ 99 * K) * TN + (C + E) * TD := by
    unfold gePhaseLowerPN
    rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyScale, hTN, hTD]
    simp only [K, C, E, Int.natCast_add, Int.natCast_mul, Int.natCast_pow,
      Int.mul_assoc]
    rfl
  have hAlg := ge_phase_lower_algebra
    (tn := TN) (td := TD) (x := X) (k := K) (c := C) (e := E)
    (by unfold K; exact Int.natCast_nonneg _) hbr
  rw [hpn, hphase]
  exact hAlg

theorem gePhaseLowerMargin_sound {m c : Nat}
    (h1 : Sc + 46 ≤ m) (h2 : m < MHI)
    (hcert : 0 ≤ evalPoly (gePhaseLowerMarginPoly c) (m : Int)) :
    PosShiftGePhaseDirectOk 320 m c := by
  let PN := evalPoly (gePhaseLowerPN c) (m : Int)
  let QD := evalPoly gePhaseLowerQD (m : Int)
  let P := posPhaseNatGe m c + lnPhaseExtraArg
  have hPNnon : 0 ≤ PN := by
    simpa [PN] using gePhaseLowerPN_nonneg (m := m) (c := c) h1 h2
  have hQDpos : 0 < QD := by
    simpa [QD] using gePhaseLowerQD_pos (m := m) h1 h2
  have hPNcast : (((PN.toNat : Nat) : Int)) = PN :=
    Int.toNat_of_nonneg hPNnon
  have hQDcast : (((QD.toNat : Nat) : Int)) = QD :=
    Int.toNat_of_nonneg (Int.le_of_lt hQDpos)
  have hY := eval_posTopXPoly m c
  have hsum : sumGE 320 PN.toNat QD.toNat (posTopX c m) (10 ^ 18) := by
    refine sumGE_of_expMarginPolyFast
      (n := 320) (m := m) (p := PN.toNat) (q := QD.toNat)
      (y := posTopX c m) (w := 10 ^ 18)
      (pn := gePhaseLowerPN c) (qd := gePhaseLowerQD) (yp := posTopXPoly c)
      ?_ ?_ ?_ ?_
    · simpa [gePhaseLowerMarginPoly, PN, QD] using hcert
    · exact hPNcast.symm
    · exact hQDcast.symm
    · exact hY
  have hqpos : 0 < QD.toNat := by
    apply Int.ofNat_lt.mp
    rw [hQDcast]
    exact hQDpos
  have harg : PN.toNat * lnErrQ ≤ P * QD.toNat := by
    apply Int.ofNat_le.mp
    simp only [Int.natCast_mul, hPNcast, hQDcast]
    have hPNle : PN ≤ (P : Int) * evalPoly geTD2b (m : Int) := by
      simpa [PN, P] using gePhaseLowerPN_le_phase_mul_TD (m := m) (c := c) h1 h2
    have hlnNon : 0 ≤ (lnErrQ : Int) := by
      unfold lnErrQ QS lnErrorBoundDen
      decide
    have hmul := Int.mul_le_mul_of_nonneg_right hPNle hlnNon
    have hQD :
        QD = (lnErrQ : Int) * evalPoly geTD2b (m : Int) := by
      unfold QD gePhaseLowerQD
      rw [evalPoly_polyScale]
    rw [hQD]
    simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hmul
  unfold PosShiftGePhaseDirectOk
  exact sumGE_arg_mono (q' := QD.toNat) hqpos harg hsum

theorem gePhaseLowerMarginVal_sound {m c : Nat}
    (h1 : Sc + 46 ≤ m) (h2 : m < MHI)
    (hcert : 0 ≤ expMarginVal 320 (evalPoly (gePhaseLowerPN c) (m : Int))
      (evalPoly gePhaseLowerQD (m : Int)) (evalPoly (posTopXPoly c) (m : Int))
      (((10 ^ 18 : Nat) : Int))) :
    PosShiftGePhaseDirectOk 320 m c := by
  let PN := evalPoly (gePhaseLowerPN c) (m : Int)
  let QD := evalPoly gePhaseLowerQD (m : Int)
  let P := posPhaseNatGe m c + lnPhaseExtraArg
  have hPNnon : 0 ≤ PN := by
    simpa [PN] using gePhaseLowerPN_nonneg (m := m) (c := c) h1 h2
  have hQDpos : 0 < QD := by
    simpa [QD] using gePhaseLowerQD_pos (m := m) h1 h2
  have hPNcast : (((PN.toNat : Nat) : Int)) = PN :=
    Int.toNat_of_nonneg hPNnon
  have hQDcast : (((QD.toNat : Nat) : Int)) = QD :=
    Int.toNat_of_nonneg (Int.le_of_lt hQDpos)
  have hY := eval_posTopXPoly m c
  have hsum : sumGE 320 PN.toNat QD.toNat (posTopX c m) (10 ^ 18) := by
    refine sumGE_of_expMarginVal
      (n := 320) (p := PN.toNat) (q := QD.toNat)
      (y := posTopX c m) (w := 10 ^ 18) ?_
    rw [hPNcast, hQDcast, ← hY]
    exact hcert
  have hqpos : 0 < QD.toNat := by
    apply Int.ofNat_lt.mp
    rw [hQDcast]
    exact hQDpos
  have harg : PN.toNat * lnErrQ ≤ P * QD.toNat := by
    apply Int.ofNat_le.mp
    simp only [Int.natCast_mul, hPNcast, hQDcast]
    have hPNle : PN ≤ (P : Int) * evalPoly geTD2b (m : Int) := by
      simpa [PN, P] using gePhaseLowerPN_le_phase_mul_TD (m := m) (c := c) h1 h2
    have hlnNon : 0 ≤ (lnErrQ : Int) := by
      unfold lnErrQ QS lnErrorBoundDen
      decide
    have hmul := Int.mul_le_mul_of_nonneg_right hPNle hlnNon
    have hQD :
        QD = (lnErrQ : Int) * evalPoly geTD2b (m : Int) := by
      unfold QD gePhaseLowerQD
      rw [evalPoly_polyScale]
    rw [hQD]
    simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hmul
  unfold PosShiftGePhaseDirectOk
  exact sumGE_arg_mono (q' := QD.toNat) hqpos harg hsum

def gePhaseLowerPNMin (c : Nat) : List Int :=
  polyAdd
    (polyScale (((2 ^ 99 * lnPhaseScaleN * lnErrorBoundDen : Nat) : Int)) geTN2b)
    (polyScale (((posConstNat c + minPosAvail : Nat) : Int)) geTD2b)

def gePhaseLowerMarginPolyMin (c : Nat) : List Int :=
  expMarginPolyFast 320 (gePhaseLowerPNMin c) gePhaseLowerQD (posTopXPoly c) (10 ^ 18)

theorem gePhaseLowerPNMin_nonneg {m c : Nat} (h1 : Sc + 46 ≤ m) (h2 : m < MHI) :
    0 ≤ evalPoly (gePhaseLowerPNMin c) (m : Int) := by
  have htn := geTN2b_nonneg_of_outer h1 h2
  have htd : 0 ≤ evalPoly geTD2b (m : Int) := by
    exact Int.le_of_lt (geTD2b_pos_of_outer h1 h2)
  unfold gePhaseLowerPNMin
  rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyScale]
  exact Int.add_nonneg
    (Int.mul_nonneg (Int.natCast_nonneg _) htn)
    (Int.mul_nonneg (Int.natCast_nonneg _) htd)

theorem gePhaseLowerPNMin_le_phase_mul_TD {m c : Nat}
    (h1 : Sc + 46 ≤ m) (h2 : m < MHI) :
    evalPoly (gePhaseLowerPNMin c) (m : Int) ≤
      ((posPhaseNatGe m c + minPosAvail : Nat) : Int) *
        evalPoly geTD2b (m : Int) := by
  have hbr := bracket_ge_lo h1 h2
  generalize hTN : evalPoly geTN2b (m : Int) = TN at hbr ⊢
  generalize hTD : evalPoly geTD2b (m : Int) = TD at hbr ⊢
  have hX := x1_nonneg_ge h1 h2
  have hphase0 := posPhaseNatGe_cast_decomp (m := m) (c := c) hX
  generalize hXV : int256 (x1W (zWord m)) = X at hbr hphase0 ⊢
  let K : Int := ((lnPhaseScaleN * lnErrorBoundDen : Nat) : Int)
  let C : Int := (posConstNat c : Int)
  let E : Int := (minPosAvail : Int)
  have hphase :
      ((posPhaseNatGe m c + minPosAvail : Nat) : Int) = X * K + C + E := by
    rw [Int.natCast_add, hphase0]
  have hpn :
      evalPoly (gePhaseLowerPNMin c) (m : Int) = (2 ^ 99 * K) * TN + (C + E) * TD := by
    unfold gePhaseLowerPNMin
    rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyScale, hTN, hTD]
    simp only [K, C, E, Int.natCast_add, Int.natCast_mul, Int.natCast_pow,
      Int.mul_assoc]
    rfl
  have hAlg := ge_phase_lower_algebra
    (tn := TN) (td := TD) (x := X) (k := K) (c := C) (e := E)
    (by unfold K; exact Int.natCast_nonneg _) hbr
  rw [hpn, hphase]
  exact hAlg

theorem gePhaseLowerMarginValMin_sound {m c : Nat}
    (h1 : Sc + 46 ≤ m) (h2 : m < MHI)
    (hcert : 0 ≤ expMarginVal 320 (evalPoly (gePhaseLowerPNMin c) (m : Int))
      (evalPoly gePhaseLowerQD (m : Int)) (evalPoly (posTopXPoly c) (m : Int))
      (((10 ^ 18 : Nat) : Int))) :
    PosShiftGeMinPhaseDirectOk 320 m c := by
  let PN := evalPoly (gePhaseLowerPNMin c) (m : Int)
  let QD := evalPoly gePhaseLowerQD (m : Int)
  let P := posPhaseNatGe m c + minPosAvail
  have hPNnon : 0 ≤ PN := by
    simpa [PN] using gePhaseLowerPNMin_nonneg (m := m) (c := c) h1 h2
  have hQDpos : 0 < QD := by
    simpa [QD] using gePhaseLowerQD_pos (m := m) h1 h2
  have hPNcast : (((PN.toNat : Nat) : Int)) = PN :=
    Int.toNat_of_nonneg hPNnon
  have hQDcast : (((QD.toNat : Nat) : Int)) = QD :=
    Int.toNat_of_nonneg (Int.le_of_lt hQDpos)
  have hY := eval_posTopXPoly m c
  have hsum : sumGE 320 PN.toNat QD.toNat (posTopX c m) (10 ^ 18) := by
    refine sumGE_of_expMarginVal
      (n := 320) (p := PN.toNat) (q := QD.toNat)
      (y := posTopX c m) (w := 10 ^ 18) ?_
    rw [hPNcast, hQDcast, ← hY]
    exact hcert
  have hqpos : 0 < QD.toNat := by
    apply Int.ofNat_lt.mp
    rw [hQDcast]
    exact hQDpos
  have harg : PN.toNat * lnErrQ ≤ P * QD.toNat := by
    apply Int.ofNat_le.mp
    simp only [Int.natCast_mul, hPNcast, hQDcast]
    have hPNle : PN ≤ (P : Int) * evalPoly geTD2b (m : Int) := by
      simpa [PN, P] using gePhaseLowerPNMin_le_phase_mul_TD (m := m) (c := c) h1 h2
    have hlnNon : 0 ≤ (lnErrQ : Int) := by
      unfold lnErrQ QS lnErrorBoundDen
      decide
    have hmul := Int.mul_le_mul_of_nonneg_right hPNle hlnNon
    have hQD :
        QD = (lnErrQ : Int) * evalPoly geTD2b (m : Int) := by
      unfold QD gePhaseLowerQD
      rw [evalPoly_polyScale]
    rw [hQD]
    simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hmul
  unfold PosShiftGeMinPhaseDirectOk
  exact sumGE_arg_mono (q' := QD.toNat) hqpos harg hsum

end LnFloorCert
