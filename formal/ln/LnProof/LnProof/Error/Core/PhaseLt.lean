import LnProof.Floor.CutEquiv
import LnProof.Error.Cert
import LnProof.Error.Core.CutDefs
import LnProof.Error.Core.ExpMargin
import LnProof.Error.Core.Residue
import LnProof.Error.Core.Budget
import LnProof.Error.Core.PhaseGe
import LnProof.Error.Core.PhaseCover

/-!
# Error bound — PhaseLt

Lt-branch phase-lower margin polynomials, cells, and covers.
-/

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

namespace LnFloorCert

open LnYul LnFloor Common.Exp Common.Poly

attribute [local irreducible] lnWadToRayBody


def ltPhaseLowerPN (c : Nat) : List Int :=
  polySub
    (polyScale (((posConstNat c + lnPhaseExtraArg : Nat) : Int)) ltTD)
    (polyScale (((2 ^ 99 * lnPhaseScaleN * lnErrorBoundDen : Nat) : Int)) ltTN)

def ltPhaseLowerQD : List Int :=
  polyScale ((lnErrQ : Nat) : Int) ltTD

def ltPhaseLowerMarginPoly (c : Nat) : List Int :=
  expMarginPolyFast 320 (ltPhaseLowerPN c) ltPhaseLowerQD (posTopXPoly c) (10 ^ 18)

def polyIvOnCell (p : List Int) (lo hi : Nat) : Int × Int :=
  hornerIv (polyShift p (lo : Int)) 0 (((hi - lo : Nat) : Int))

def gePhaseLowerIvCellOkB (lo hi c : Nat) : Bool :=
  decide (Sc + 46 ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < MHI) &&
        decide (c < 160) &&
          let pIv := polyIvOnCell (gePhaseLowerPN c) lo hi
          let qIv := polyIvOnCell gePhaseLowerQD lo hi
          let yIv := polyIvOnCell (posTopXPoly c) lo hi
          decide (0 ≤ pIv.1) &&
            decide (0 ≤ qIv.1) &&
              decide (0 ≤ expMarginIvLower 320 pIv qIv yIv (10 ^ 18))

def ltPhaseLowerIvCellOkB (lo hi c : Nat) : Bool :=
  decide (MLO ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi + 46 ≤ Sc) &&
        decide (c < 160) &&
          let pIv := polyIvOnCell (ltPhaseLowerPN c) lo hi
          let qIv := polyIvOnCell ltPhaseLowerQD lo hi
          let yIv := polyIvOnCell (posTopXPoly c) lo hi
          decide (0 ≤ pIv.1) &&
            decide (0 ≤ qIv.1) &&
              decide (0 ≤ expMarginIvLower 320 pIv qIv yIv (10 ^ 18))

theorem ltTD_pos_of_outer {m : Nat} (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) :
    0 < evalPoly ltTD (m : Int) := by
  have hw1 : (39614081257132168796771975168 : Int) ≤ (m : Int) := by
    simp only [MLO] at h1
    omega
  have hw2 : (m : Int) ≤ 56022770974786139918731938181 := by
    simp only [Sc] at h2
    omega
  have h := ltTD_nonneg hw1 hw2
  rw [evalCertLtTD] at h
  omega

theorem ltPhaseLowerQD_pos {m : Nat} (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) :
    0 < evalPoly ltPhaseLowerQD (m : Int) := by
  unfold ltPhaseLowerQD
  rw [evalPoly_polyScale]
  exact Int.mul_pos (by unfold lnErrQ QS lnErrorBoundDen; decide)
    (ltTD_pos_of_outer h1 h2)

theorem posPhaseNatLt_cast_decomp {m c : Nat}
    (hX : int256 (x1W (zWord m)) ≤ 0)
    (hneg : posNegXNat m ≤ posConstNat c) :
    ((posPhaseNatLt m c : Nat) : Int) =
      (posConstNat c : Int) -
        (-int256 (x1W (zWord m))) *
          ((lnPhaseScaleN * lnErrorBoundDen : Nat) : Int) := by
  have hnegc : ((posNegXNat m : Nat) : Int) =
      (-int256 (x1W (zWord m))) *
        ((lnPhaseScaleN * lnErrorBoundDen : Nat) : Int) := by
    rw [posNegXNat_cast (m := m) hX]
    change ((-int256 (x1W (zWord m))) * ((lnPhaseScaleN : Nat) : Int)) *
        ((lnErrorBoundDen : Nat) : Int) =
      (-int256 (x1W (zWord m))) * ((lnPhaseScaleN * lnErrorBoundDen : Nat) : Int)
    rw [Int.natCast_mul]
    rw [Int.mul_assoc]
  have hsub : ((posConstNat c - posNegXNat m : Nat) : Int) =
      ((posConstNat c : Nat) : Int) - ((posNegXNat m : Nat) : Int) := by
    omega
  unfold posPhaseNatLt
  rw [hsub, hnegc]

theorem lt_phase_lower_algebra {tn td neg k c e : Int}
    (hk : 0 ≤ k) (hbr : neg * td ≤ tn * 2 ^ 99) :
    (c + e) * td - (2 ^ 99 * k) * tn ≤
      (c - neg * k + e) * td := by
  have hmul := Int.mul_le_mul_of_nonneg_right hbr hk
  have hmul' : neg * td * k ≤ (2 ^ 99 * k) * tn := by
    simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hmul
  have hrewrite : (c + e) * td - neg * td * k = (c - neg * k + e) * td := by
    rw [Int.add_mul, Int.add_mul, Int.sub_mul]
    have hterm : neg * td * k = neg * k * td := by
      rw [Int.mul_assoc, Int.mul_comm td k, ← Int.mul_assoc]
    rw [hterm]
    omega
  calc
    (c + e) * td - (2 ^ 99 * k) * tn ≤
        (c + e) * td - neg * td * k := by
      exact Int.sub_le_sub_left hmul' ((c + e) * td)
    _ = (c - neg * k + e) * td := hrewrite

theorem ltPhaseLowerPN_le_phase_mul_TD {m c : Nat}
    (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) (hc : c < 160) :
    evalPoly (ltPhaseLowerPN c) (m : Int) ≤
      ((posPhaseNatLt m c + lnPhaseExtraArg : Nat) : Int) *
        evalPoly ltTD (m : Int) := by
  have hbr := bracket_lt_up h1 h2
  generalize hTN : evalPoly ltTN (m : Int) = TN at hbr ⊢
  generalize hTD : evalPoly ltTD (m : Int) = TD at hbr ⊢
  have hX := x1_nonpos_lt h1 h2
  have hmhi : m < MHI := by
    simp only [Sc, MHI] at h2 ⊢
    omega
  have hV0 : 0 ≤ int256 (x1W (zWord m)) * 7450580596923828125 +
      ln2kInt c + lnBiasI := by
    simpa [posAccI] using posAccI_nonneg h1 hmhi hc
  have hneg := posNegXNat_le_posConstNat hX (Nat.le_of_lt hc) hV0
  have hphase0 := posPhaseNatLt_cast_decomp (m := m) (c := c) hX hneg
  generalize hNegV : -int256 (x1W (zWord m)) = X at hbr hphase0 ⊢
  let K : Int := ((lnPhaseScaleN * lnErrorBoundDen : Nat) : Int)
  let C : Int := (posConstNat c : Int)
  let E : Int := (lnPhaseExtraArg : Int)
  have hphase :
      ((posPhaseNatLt m c + lnPhaseExtraArg : Nat) : Int) = C - X * K + E := by
    rw [Int.natCast_add, hphase0]
  have hpn :
      evalPoly (ltPhaseLowerPN c) (m : Int) = (C + E) * TD - (2 ^ 99 * K) * TN := by
    unfold ltPhaseLowerPN polySub
    rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyNeg, evalPoly_polyScale,
      hTN, hTD]
    simp only [K, C, E, Int.natCast_add, Int.natCast_mul, Int.natCast_pow,
      Int.mul_assoc]
    rfl
  have hAlg := lt_phase_lower_algebra
    (tn := TN) (td := TD) (neg := X) (k := K) (c := C) (e := E)
    (by unfold K; exact Int.natCast_nonneg _) hbr
  rw [hpn, hphase]
  exact hAlg

theorem ltPhaseLowerMargin_sound {m c : Nat}
    (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) (hc : c < 160)
    (hpn_nonneg : 0 ≤ evalPoly (ltPhaseLowerPN c) (m : Int))
    (hcert : 0 ≤ evalPoly (ltPhaseLowerMarginPoly c) (m : Int)) :
    PosShiftLtPhaseDirectOk 320 m c := by
  let PN := evalPoly (ltPhaseLowerPN c) (m : Int)
  let QD := evalPoly ltPhaseLowerQD (m : Int)
  let P := posPhaseNatLt m c + lnPhaseExtraArg
  have hPNnon : 0 ≤ PN := by
    simpa [PN] using hpn_nonneg
  have hQDpos : 0 < QD := by
    simpa [QD] using ltPhaseLowerQD_pos (m := m) h1 h2
  have hPNcast : (((PN.toNat : Nat) : Int)) = PN :=
    Int.toNat_of_nonneg hPNnon
  have hQDcast : (((QD.toNat : Nat) : Int)) = QD :=
    Int.toNat_of_nonneg (Int.le_of_lt hQDpos)
  have hY := eval_posTopXPoly m c
  have hsum : sumGE 320 PN.toNat QD.toNat (posTopX c m) (10 ^ 18) := by
    refine sumGE_of_expMarginPolyFast
      (n := 320) (m := m) (p := PN.toNat) (q := QD.toNat)
      (y := posTopX c m) (w := 10 ^ 18)
      (pn := ltPhaseLowerPN c) (qd := ltPhaseLowerQD) (yp := posTopXPoly c)
      ?_ ?_ ?_ ?_
    · change 0 ≤ evalPoly (ltPhaseLowerMarginPoly c) (m : Int)
      exact hcert
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
    have hPNle : PN ≤ (P : Int) * evalPoly ltTD (m : Int) := by
      change evalPoly (ltPhaseLowerPN c) (m : Int) ≤
        ((posPhaseNatLt m c + lnPhaseExtraArg : Nat) : Int) * evalPoly ltTD (m : Int)
      exact ltPhaseLowerPN_le_phase_mul_TD (m := m) (c := c) h1 h2 hc
    have hlnNon : 0 ≤ (lnErrQ : Int) := by
      unfold lnErrQ QS lnErrorBoundDen
      decide
    have hmul := Int.mul_le_mul_of_nonneg_right hPNle hlnNon
    have hQD :
        QD = (lnErrQ : Int) * evalPoly ltTD (m : Int) := by
      unfold QD ltPhaseLowerQD
      rw [evalPoly_polyScale]
    rw [hQD]
    simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hmul
  unfold PosShiftLtPhaseDirectOk
  exact sumGE_arg_mono (q' := QD.toNat) hqpos harg hsum

theorem ltPhaseLowerMarginVal_sound {m c : Nat}
    (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) (hc : c < 160)
    (hpn_nonneg : 0 ≤ evalPoly (ltPhaseLowerPN c) (m : Int))
    (hcert : 0 ≤ expMarginVal 320 (evalPoly (ltPhaseLowerPN c) (m : Int))
      (evalPoly ltPhaseLowerQD (m : Int)) (evalPoly (posTopXPoly c) (m : Int))
      (((10 ^ 18 : Nat) : Int))) :
    PosShiftLtPhaseDirectOk 320 m c := by
  let PN := evalPoly (ltPhaseLowerPN c) (m : Int)
  let QD := evalPoly ltPhaseLowerQD (m : Int)
  let P := posPhaseNatLt m c + lnPhaseExtraArg
  have hPNnon : 0 ≤ PN := by
    simpa [PN] using hpn_nonneg
  have hQDpos : 0 < QD := by
    simpa [QD] using ltPhaseLowerQD_pos (m := m) h1 h2
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
    have hPNle : PN ≤ (P : Int) * evalPoly ltTD (m : Int) := by
      change evalPoly (ltPhaseLowerPN c) (m : Int) ≤
        ((posPhaseNatLt m c + lnPhaseExtraArg : Nat) : Int) * evalPoly ltTD (m : Int)
      exact ltPhaseLowerPN_le_phase_mul_TD (m := m) (c := c) h1 h2 hc
    have hlnNon : 0 ≤ (lnErrQ : Int) := by
      unfold lnErrQ QS lnErrorBoundDen
      decide
    have hmul := Int.mul_le_mul_of_nonneg_right hPNle hlnNon
    have hQD :
        QD = (lnErrQ : Int) * evalPoly ltTD (m : Int) := by
      unfold QD ltPhaseLowerQD
      rw [evalPoly_polyScale]
    rw [hQD]
    simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hmul
  unfold PosShiftLtPhaseDirectOk
  exact sumGE_arg_mono (q' := QD.toNat) hqpos harg hsum

def ltPhaseLowerPNMin (c : Nat) : List Int :=
  polySub
    (polyScale (((posConstNat c + minPosAvail : Nat) : Int)) ltTD)
    (polyScale (((2 ^ 99 * lnPhaseScaleN * lnErrorBoundDen : Nat) : Int)) ltTN)

def ltPhaseLowerMarginPolyMin (c : Nat) : List Int :=
  expMarginPolyFast 320 (ltPhaseLowerPNMin c) ltPhaseLowerQD (posTopXPoly c) (10 ^ 18)

theorem ltPhaseLowerPNMin_le_phase_mul_TD {m c : Nat}
    (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) (hc : c < 160) :
    evalPoly (ltPhaseLowerPNMin c) (m : Int) ≤
      ((posPhaseNatLt m c + minPosAvail : Nat) : Int) *
        evalPoly ltTD (m : Int) := by
  have hbr := bracket_lt_up h1 h2
  generalize hTN : evalPoly ltTN (m : Int) = TN at hbr ⊢
  generalize hTD : evalPoly ltTD (m : Int) = TD at hbr ⊢
  have hX := x1_nonpos_lt h1 h2
  have hmhi : m < MHI := by
    simp only [Sc, MHI] at h2 ⊢
    omega
  have hV0 : 0 ≤ int256 (x1W (zWord m)) * 7450580596923828125 +
      ln2kInt c + lnBiasI := by
    simpa [posAccI] using posAccI_nonneg h1 hmhi hc
  have hneg := posNegXNat_le_posConstNat hX (Nat.le_of_lt hc) hV0
  have hphase0 := posPhaseNatLt_cast_decomp (m := m) (c := c) hX hneg
  generalize hNegV : -int256 (x1W (zWord m)) = X at hbr hphase0 ⊢
  let K : Int := ((lnPhaseScaleN * lnErrorBoundDen : Nat) : Int)
  let C : Int := (posConstNat c : Int)
  let E : Int := (minPosAvail : Int)
  have hphase :
      ((posPhaseNatLt m c + minPosAvail : Nat) : Int) = C - X * K + E := by
    rw [Int.natCast_add, hphase0]
  have hpn :
      evalPoly (ltPhaseLowerPNMin c) (m : Int) = (C + E) * TD - (2 ^ 99 * K) * TN := by
    unfold ltPhaseLowerPNMin polySub
    rw [evalPoly_polyAdd, evalPoly_polyScale, evalPoly_polyNeg, evalPoly_polyScale,
      hTN, hTD]
    simp only [K, C, E, Int.natCast_add, Int.natCast_mul, Int.natCast_pow,
      Int.mul_assoc]
    rfl
  have hAlg := lt_phase_lower_algebra
    (tn := TN) (td := TD) (neg := X) (k := K) (c := C) (e := E)
    (by unfold K; exact Int.natCast_nonneg _) hbr
  rw [hpn, hphase]
  exact hAlg

theorem ltPhaseLowerMarginValMin_sound {m c : Nat}
    (h1 : MLO ≤ m) (h2 : m + 46 ≤ Sc) (hc : c < 160)
    (hpn_nonneg : 0 ≤ evalPoly (ltPhaseLowerPNMin c) (m : Int))
    (hcert : 0 ≤ expMarginVal 320 (evalPoly (ltPhaseLowerPNMin c) (m : Int))
      (evalPoly ltPhaseLowerQD (m : Int)) (evalPoly (posTopXPoly c) (m : Int))
      (((10 ^ 18 : Nat) : Int))) :
    PosShiftLtMinPhaseDirectOk 320 m c := by
  let PN := evalPoly (ltPhaseLowerPNMin c) (m : Int)
  let QD := evalPoly ltPhaseLowerQD (m : Int)
  let P := posPhaseNatLt m c + minPosAvail
  have hPNnon : 0 ≤ PN := by
    simpa [PN] using hpn_nonneg
  have hQDpos : 0 < QD := by
    simpa [QD] using ltPhaseLowerQD_pos (m := m) h1 h2
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
    have hPNle : PN ≤ (P : Int) * evalPoly ltTD (m : Int) := by
      change evalPoly (ltPhaseLowerPNMin c) (m : Int) ≤
        ((posPhaseNatLt m c + minPosAvail : Nat) : Int) * evalPoly ltTD (m : Int)
      exact ltPhaseLowerPNMin_le_phase_mul_TD (m := m) (c := c) h1 h2 hc
    have hlnNon : 0 ≤ (lnErrQ : Int) := by
      unfold lnErrQ QS lnErrorBoundDen
      decide
    have hmul := Int.mul_le_mul_of_nonneg_right hPNle hlnNon
    have hQD :
        QD = (lnErrQ : Int) * evalPoly ltTD (m : Int) := by
      unfold QD ltPhaseLowerQD
      rw [evalPoly_polyScale]
    rw [hQD]
    simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hmul
  unfold PosShiftLtMinPhaseDirectOk
  exact sumGE_arg_mono (q' := QD.toNat) hqpos harg hsum

structure GePhaseLowerCell where
  lo : Nat
  hi : Nat
  marginWs : List Int

structure LtPhaseLowerCell where
  lo : Nat
  hi : Nat
  pnWs : List Int
  marginWs : List Int

def gePhaseLowerCellOkB (cell : GePhaseLowerCell) (c : Nat) : Bool :=
  decide (Sc + 46 ≤ cell.lo) &&
    decide (cell.lo ≤ cell.hi) &&
      decide (cell.hi < MHI) &&
        decide (c < 160) &&
          shiftedExpMarginCellOkB kB 320 (gePhaseLowerPN c) gePhaseLowerQD
            (posTopXPoly c) cell.lo cell.hi (10 ^ 18) cell.marginWs

def ltPhaseLowerCellOkB (cell : LtPhaseLowerCell) (c : Nat) : Bool :=
  decide (MLO ≤ cell.lo) &&
    decide (cell.lo ≤ cell.hi) &&
      decide (cell.hi + 46 ≤ Sc) &&
        decide (c < 160) &&
          checkCoverK kB (ltPhaseLowerPN c) (cell.lo : Int) (cell.hi : Int) cell.pnWs &&
            shiftedExpMarginCellOkB kB 320 (ltPhaseLowerPN c) ltPhaseLowerQD
              (posTopXPoly c) cell.lo cell.hi (10 ^ 18) cell.marginWs

theorem gePhaseLowerCell_sound {cell : GePhaseLowerCell} {m c : Nat}
    (h : gePhaseLowerCellOkB cell c = true)
    (hlom : cell.lo ≤ m) (hmhi : m ≤ cell.hi) :
    PosShiftGePhaseDirectOk 320 m c := by
  unfold gePhaseLowerCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, _hlohi⟩, hhi⟩, _hc⟩, hmargin⟩ := h
  exact gePhaseLowerMarginVal_sound (by omega : Sc + 46 ≤ m) (by omega : m < MHI)
    (shiftedExpMarginCellOkB_sound hmargin hlom hmhi)

theorem ltPhaseLowerCell_sound {cell : LtPhaseLowerCell} {m c : Nat}
    (h : ltPhaseLowerCellOkB cell c = true)
    (hlom : cell.lo ≤ m) (hmhi : m ≤ cell.hi) :
    PosShiftLtPhaseDirectOk 320 m c := by
  unfold ltPhaseLowerCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hlo, _hlohi⟩, hhi⟩, hc⟩, hpn⟩, hmargin⟩ := h
  exact ltPhaseLowerMarginVal_sound (by omega : MLO ≤ m) (by omega : m + 46 ≤ Sc) hc
    (checkCoverK_sound _ _ _ _ _ hpn (m : Int) (by omega) (by omega))
    (shiftedExpMarginCellOkB_sound hmargin hlom hmhi)

def gePhaseLowerCellListCoverB (c : Nat) : Nat → Nat → List GePhaseLowerCell → Bool
  | lo, hi, [] => decide (hi < lo)
  | lo, hi, cell :: cells =>
      decide (cell.lo = lo) &&
        decide (lo ≤ cell.hi) &&
          decide (cell.hi ≤ hi) &&
            gePhaseLowerCellOkB cell c &&
              gePhaseLowerCellListCoverB c (cell.hi + 1) hi cells

def ltPhaseLowerCellListCoverB (c : Nat) : Nat → Nat → List LtPhaseLowerCell → Bool
  | lo, hi, [] => decide (hi < lo)
  | lo, hi, cell :: cells =>
      decide (cell.lo = lo) &&
        decide (lo ≤ cell.hi) &&
          decide (cell.hi ≤ hi) &&
            ltPhaseLowerCellOkB cell c &&
              ltPhaseLowerCellListCoverB c (cell.hi + 1) hi cells

theorem gePhaseLowerCellListCoverB_sound {cells : List GePhaseLowerCell} {c lo hi m : Nat}
    (h : gePhaseLowerCellListCoverB c lo hi cells = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGePhaseDirectOk 320 m c := by
  induction cells generalizing lo with
  | nil =>
      unfold gePhaseLowerCellListCoverB at h
      have hlt : hi < lo := of_decide_eq_true h
      omega
  | cons cell cells ih =>
      unfold gePhaseLowerCellListCoverB at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hlo, _hlohi⟩, _hhihi⟩, hok⟩, hrest⟩ := h
      by_cases hmcell : m ≤ cell.hi
      · exact gePhaseLowerCell_sound hok (by omega) hmcell
      · exact ih hrest (by omega)

theorem ltPhaseLowerCellListCoverB_sound {cells : List LtPhaseLowerCell} {c lo hi m : Nat}
    (h : ltPhaseLowerCellListCoverB c lo hi cells = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftLtPhaseDirectOk 320 m c := by
  induction cells generalizing lo with
  | nil =>
      unfold ltPhaseLowerCellListCoverB at h
      have hlt : hi < lo := of_decide_eq_true h
      omega
  | cons cell cells ih =>
      unfold ltPhaseLowerCellListCoverB at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hlo, _hlohi⟩, _hhihi⟩, hok⟩, hrest⟩ := h
      by_cases hmcell : m ≤ cell.hi
      · exact ltPhaseLowerCell_sound hok (by omega) hmcell
      · exact ih hrest (by omega)

end LnFloorCert
