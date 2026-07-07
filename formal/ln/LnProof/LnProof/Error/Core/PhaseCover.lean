import LnProof.Floor.CutEquiv
import LnProof.Error.Cert
import LnProof.Error.Core.CutDefs
import LnProof.Error.Core.Args
import LnProof.Error.Core.Residue
import LnProof.Error.Core.Budget
import LnProof.Error.Core.Direct

/-!
# Error bound — PhaseCover

Phase cell deciders / covers and the `posPhaseNat*` casts into `lnErrArg`.
-/

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

namespace LnFloorCert

open LnYul LnFloor Common.Exp Common.Poly

attribute [local irreducible] lnWadToRayBody


def gePhaseCellOkB (lo hi c : Nat) : Bool :=
  decide (Sc ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < MHI) &&
        decide (c < 160) &&
          sumGEB 320 (posPhaseNatGe lo c + lnPhaseExtraArg) lnErrQ
            (posTopX c hi) (10 ^ 18)

def ltPhaseCellOkB (lo hi c : Nat) : Bool :=
  decide (MLO ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < Sc) &&
        decide (c < 160) &&
          sumGEB 320 (posPhaseNatLt lo c + lnPhaseExtraArg) lnErrQ
            (posTopX c hi) (10 ^ 18)

def gePhaseGapCellOkB (lo hi c : Nat) : Bool :=
  decide (Sc ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < MHI) &&
        decide (c < 160) &&
          sumGEB 320 (posPhaseNatGe lo c + lnPhaseExtraArg + lnDirectGapArg)
            lnErrQ (posTopX c hi) (10 ^ 18)

def ltPhaseGapCellOkB (lo hi c : Nat) : Bool :=
  decide (MLO ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < Sc) &&
        decide (c < 160) &&
          sumGEB 320 (posPhaseNatLt lo c + lnPhaseExtraArg + lnDirectGapArg)
            lnErrQ (posTopX c hi) (10 ^ 18)

def geTopBudgetCoarseCellOkB (lo hi c : Nat) : Bool :=
  decide (Sc ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < MHI) &&
        decide (c < 160) &&
          decide (wadRayNum (posTopX c hi) * (posBaseWGe c * lnErrQ) ≤
            (posBaseYGe lo c * (lnErrQ + minPosAvail)) * wadRayStrictDen)

def ltTopBudgetCoarseCellOkB (lo hi c : Nat) : Bool :=
  decide (MLO ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < Sc) &&
        decide (c < 160) &&
          decide (wadRayNum (posTopX c hi) * (posBaseWLt c * lnErrQ) ≤
            (posBaseYLt lo c * (lnErrQ + minPosAvail)) * wadRayStrictDen)

def geTopBudgetRunCellOkB (lo hi c : Nat) : Bool :=
  decide (Sc ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < MHI) &&
        decide (c < 160) &&
          let rlo := int256 (lnTail (evmSub 160 c) lo)
          decide (posAccI hi c < (rlo + 1) * twoPow72I) &&
            decide (wadRayNum (posTopX c hi) * (posBaseWGe c * lnErrQ) ≤
              (posBaseYGe lo c * (lnErrQ + posAvailGe hi c rlo)) * wadRayStrictDen)

def ltTopBudgetRunCellOkB (lo hi c : Nat) : Bool :=
  decide (MLO ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < Sc) &&
        decide (c < 160) &&
          let rlo := int256 (lnTail (evmSub 160 c) lo)
          decide (posAccI hi c < (rlo + 1) * twoPow72I) &&
            decide (wadRayNum (posTopX c hi) * (posBaseWLt c * lnErrQ) ≤
              (posBaseYLt lo c * (lnErrQ + posAvailLt hi c rlo)) * wadRayStrictDen)

theorem gePhaseCell_sound {lo hi m c : Nat} (h : gePhaseCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGePhaseDirectOk 320 m c := by
  unfold gePhaseCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, _hlohi⟩, hhi⟩, _hc⟩, hsum⟩ := h
  unfold PosShiftGePhaseDirectOk
  refine sumGE_exact_mono (n := 320)
    (p0 := posPhaseNatGe lo c + lnPhaseExtraArg)
    (p := posPhaseNatGe m c + lnPhaseExtraArg)
    (y0 := posTopX c hi) (y := posTopX c m) ?_ ?_ (sumGE_of_sumGEB hsum)
  · exact Nat.add_le_add_right
      (posPhaseNatGe_mono_m hlo hlom (by omega)) lnPhaseExtraArg
  · exact posTopX_mono_m hmhi

theorem ltPhaseCell_sound {lo hi m c : Nat} (h : ltPhaseCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftLtPhaseDirectOk 320 m c := by
  unfold ltPhaseCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, _hlohi⟩, hhi⟩, _hc⟩, hsum⟩ := h
  unfold PosShiftLtPhaseDirectOk
  refine sumGE_exact_mono (n := 320)
    (p0 := posPhaseNatLt lo c + lnPhaseExtraArg)
    (p := posPhaseNatLt m c + lnPhaseExtraArg)
    (y0 := posTopX c hi) (y := posTopX c m) ?_ ?_ (sumGE_of_sumGEB hsum)
  · exact Nat.add_le_add_right
      (posPhaseNatLt_mono_m hlo hlom (by simp only [Sc, MHI] at hhi ⊢; omega))
      lnPhaseExtraArg
  · exact posTopX_mono_m hmhi

theorem gePhaseGapCell_sound {lo hi m c : Nat}
    (h : gePhaseGapCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGePhaseGapDirectOk 320 m c := by
  unfold gePhaseGapCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, _hlohi⟩, hhi⟩, _hc⟩, hsum⟩ := h
  unfold PosShiftGePhaseGapDirectOk
  refine sumGE_exact_mono (n := 320)
    (p0 := posPhaseNatGe lo c + lnPhaseExtraArg + lnDirectGapArg)
    (p := posPhaseNatGe m c + lnPhaseExtraArg + lnDirectGapArg)
    (y0 := posTopX c hi) (y := posTopX c m) ?_ ?_ (sumGE_of_sumGEB hsum)
  · exact Nat.add_le_add_right
      (Nat.add_le_add_right (posPhaseNatGe_mono_m hlo hlom (by omega))
        lnPhaseExtraArg) lnDirectGapArg
  · exact posTopX_mono_m hmhi

theorem ltPhaseGapCell_sound {lo hi m c : Nat}
    (h : ltPhaseGapCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftLtPhaseGapDirectOk 320 m c := by
  unfold ltPhaseGapCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, _hlohi⟩, hhi⟩, _hc⟩, hsum⟩ := h
  unfold PosShiftLtPhaseGapDirectOk
  refine sumGE_exact_mono (n := 320)
    (p0 := posPhaseNatLt lo c + lnPhaseExtraArg + lnDirectGapArg)
    (p := posPhaseNatLt m c + lnPhaseExtraArg + lnDirectGapArg)
    (y0 := posTopX c hi) (y := posTopX c m) ?_ ?_ (sumGE_of_sumGEB hsum)
  · exact Nat.add_le_add_right
      (Nat.add_le_add_right
        (posPhaseNatLt_mono_m hlo hlom (by simp only [Sc, MHI] at hhi ⊢; omega))
        lnPhaseExtraArg) lnDirectGapArg
  · exact posTopX_mono_m hmhi

def phaseSearchFuel : Nat := 128
def phaseCoverFuel : Nat := 20000

def lnErrorHardMantissa : Nat := 39770979022059719714796403827

def phaseSearchMax (fuel : Nat) (ok : Nat → Bool) (lo hi best : Nat) : Nat :=
  match fuel with
  | 0 => best
  | fuel + 1 =>
      if lo ≤ hi then
        let mid := (lo + hi) / 2
        if ok mid then
          phaseSearchMax fuel ok (mid + 1) hi mid
        else
          phaseSearchMax fuel ok lo (mid - 1) best
      else
        best

def gePhaseCoverB : Nat → Nat → Nat → Nat → Bool
  | 0, _c, lo, hi => decide (hi < lo)
  | fuel + 1, c, lo, hi =>
      if hi < lo then
        true
      else
        let mx := phaseSearchMax phaseSearchFuel (fun h => gePhaseCellOkB lo h c)
          lo hi (lo - 1)
        decide (lo ≤ mx) &&
          decide (mx ≤ hi) &&
            gePhaseCellOkB lo mx c &&
              gePhaseCoverB fuel c (mx + 1) hi

def ltPhaseCoverB : Nat → Nat → Nat → Nat → Bool
  | 0, _c, lo, hi => decide (hi < lo)
  | fuel + 1, c, lo, hi =>
      if hi < lo then
        true
      else if lo = lnErrorHardMantissa then
        ltPhaseCoverB fuel c (lo + 1) hi
      else
        let mx := phaseSearchMax phaseSearchFuel (fun h => ltPhaseCellOkB lo h c)
          lo hi (lo - 1)
        decide (lo ≤ mx) &&
          decide (mx ≤ hi) &&
            ltPhaseCellOkB lo mx c &&
              ltPhaseCoverB fuel c (mx + 1) hi

theorem gePhaseCoverB_sound {fuel c lo hi m : Nat}
    (h : gePhaseCoverB fuel c lo hi = true) (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGePhaseDirectOk 320 m c := by
  revert lo
  induction fuel with
  | zero =>
      intro lo h hlom
      unfold gePhaseCoverB at h
      simp only [decide_eq_true_eq] at h
      omega
  | succ fuel ih =>
      intro lo h hlom
      unfold gePhaseCoverB at h
      by_cases hdone : hi < lo
      · rw [if_pos hdone] at h
        omega
      · rw [if_neg hdone] at h
        let mx := phaseSearchMax phaseSearchFuel (fun h => gePhaseCellOkB lo h c)
          lo hi (lo - 1)
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨hlmx, hmxhi⟩, hcell⟩, hrest⟩ := h
        by_cases hleft : m ≤ mx
        · exact gePhaseCell_sound hcell hlom hleft
        · exact ih (lo := mx + 1) hrest (by omega)

theorem ltPhaseCoverB_sound {fuel c lo hi m : Nat}
    (h : ltPhaseCoverB fuel c lo hi = true) (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    m = lnErrorHardMantissa ∨ PosShiftLtPhaseDirectOk 320 m c := by
  revert lo
  induction fuel with
  | zero =>
      intro lo h hlom
      unfold ltPhaseCoverB at h
      simp only [decide_eq_true_eq] at h
      omega
  | succ fuel ih =>
      intro lo h hlom
      unfold ltPhaseCoverB at h
      by_cases hdone : hi < lo
      · rw [if_pos hdone] at h
        omega
      · rw [if_neg hdone] at h
        by_cases hhard : lo = lnErrorHardMantissa
        · rw [if_pos hhard] at h
          by_cases hm : m = lo
          · exact Or.inl (by omega)
          · exact ih (lo := lo + 1) h (by omega)
        · rw [if_neg hhard] at h
          let mx := phaseSearchMax phaseSearchFuel (fun h => ltPhaseCellOkB lo h c)
            lo hi (lo - 1)
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨⟨hlmx, hmxhi⟩, hcell⟩, hrest⟩ := h
          by_cases hleft : m ≤ mx
          · exact Or.inr (ltPhaseCell_sound hcell hlom hleft)
          · exact ih (lo := mx + 1) hrest (by omega)

structure PhaseCell where
  lo : Nat
  hi : Nat

def gePhaseCellListCoverB (c : Nat) : Nat → Nat → List PhaseCell → Bool
  | lo, hi, [] => decide (hi < lo)
  | lo, hi, cell :: cells =>
      decide (cell.lo = lo) &&
        decide (lo ≤ cell.hi) &&
          decide (cell.hi ≤ hi) &&
            gePhaseCellOkB cell.lo cell.hi c &&
              gePhaseCellListCoverB c (cell.hi + 1) hi cells

def ltPhaseCellListCoverB (c : Nat) : Nat → Nat → List PhaseCell → Bool
  | lo, hi, [] => decide (hi < lo)
  | lo, hi, cell :: cells =>
      decide (cell.lo = lo) &&
        decide (lo ≤ cell.hi) &&
          decide (cell.hi ≤ hi) &&
            ltPhaseCellOkB cell.lo cell.hi c &&
              ltPhaseCellListCoverB c (cell.hi + 1) hi cells

theorem gePhaseCellListCoverB_sound {cells : List PhaseCell} {c lo hi m : Nat}
    (h : gePhaseCellListCoverB c lo hi cells = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGePhaseDirectOk 320 m c := by
  induction cells generalizing lo with
  | nil =>
      unfold gePhaseCellListCoverB at h
      have hlt : hi < lo := of_decide_eq_true h
      omega
  | cons cell cells ih =>
      unfold gePhaseCellListCoverB at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hlo, _hlohi⟩, _hhihi⟩, hok⟩, hrest⟩ := h
      by_cases hmcell : m ≤ cell.hi
      · exact gePhaseCell_sound hok (by omega) hmcell
      · exact ih hrest (by omega)

theorem ltPhaseCellListCoverB_sound {cells : List PhaseCell} {c lo hi m : Nat}
    (h : ltPhaseCellListCoverB c lo hi cells = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftLtPhaseDirectOk 320 m c := by
  induction cells generalizing lo with
  | nil =>
      unfold ltPhaseCellListCoverB at h
      have hlt : hi < lo := of_decide_eq_true h
      omega
  | cons cell cells ih =>
      unfold ltPhaseCellListCoverB at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hlo, _hlohi⟩, _hhihi⟩, hok⟩, hrest⟩ := h
      by_cases hmcell : m ≤ cell.hi
      · exact ltPhaseCell_sound hok (by omega) hmcell
      · exact ih hrest (by omega)

theorem posPhaseI_le_of_floor {m c : Nat} {r : Int} (hc : c ≤ 160)
    (hr : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI < (r + 1) * 2 ^ 72) :
    posPhaseI m c ≤ (r + 1) * twoPow99I - twoPow27I := by
  have h := phase_lt_scaled_le hr
  change (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI) * twoPow27I ≤ ((r + 1) * twoPow72I - 1) * twoPow27I at h
  have hVs := v_scale_pos (int256 (x1W (zWord m))) c hc
  have hVs' :
      (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
          lnBiasI) * twoPow27I =
        int256 (x1W (zWord m)) * lnPhaseScaleI +
          ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
            lnBiasI * twoPow27I := by
    simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
  rw [hVs'] at h
  have er : ((r + 1) * twoPow72I - 1) * twoPow27I =
      (r + 1) * twoPow99I - twoPow27I := by
    unfold twoPow72I twoPow27I twoPow99I
    rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
      by decide]
    omega
  rw [er] at h
  simpa [posPhaseI, lnPhaseScaleI, twoPow27I, lnBiasI] using h

theorem posPhaseNatGe_cast {m c : Nat}
    (hX : 0 ≤ int256 (x1W (zWord m))) :
    ((posPhaseNatGe m c : Nat) : Int) =
      posPhaseI m c * (lnErrorBoundDen : Int) := by
  have hXn : (((int256 (x1W (zWord m))).toNat : Nat) : Int) =
      int256 (x1W (zWord m)) :=
    Int.toNat_of_nonneg hX
  have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
    simp only [Int.natCast_mul]
    rfl
  have hLc : (((160 - c) * (LN2c * twoPow27N) : Nat) : Int) =
      ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) := by
    simp only [Int.natCast_mul]
    unfold twoPow27N twoPow27I
    rfl
  have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
    unfold lnErrorBoundDen
    rfl
  have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
  have hN : (((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
      (((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I)) *
        (1000000000 : Int) := by
    rw [show (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
        ((160 - c) * (LN2c * twoPow27N)) * lnErrorBoundDen by
          simp only [Nat.mul_assoc]]
    simp only [Int.natCast_mul, hLc, hden]
  unfold posPhaseNatGe posPhaseI
  simp only [Int.natCast_add, Int.natCast_mul, hXn, hBc, hN, hden, hscale]
  rw [Int.add_mul, Int.add_mul]

theorem posConstNat_cast (c : Nat) :
    ((posConstNat c : Nat) : Int) =
      (((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
        lnBiasI * twoPow27I) * (lnErrorBoundDen : Int) := by
  have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
    unfold twoPow27N twoPow27I lnBiasI
    decide +kernel
  have hLc : (((160 - c) * (LN2c * twoPow27N) : Nat) : Int) =
      ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) := by
    simp only [Int.natCast_mul]
    unfold twoPow27N twoPow27I
    rfl
  have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
    unfold lnErrorBoundDen
    rfl
  have hN : (((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
      (((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I)) *
        (1000000000 : Int) := by
    rw [show (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
        ((160 - c) * (LN2c * twoPow27N)) * lnErrorBoundDen by
          simp only [Nat.mul_assoc]]
    simp only [Int.natCast_mul, hLc, hden]
  unfold posConstNat
  simp only [Int.natCast_add, Int.natCast_mul, hBc, hN, hden]
  rw [Int.add_mul]

theorem posNegXNat_cast {m : Nat}
    (hX : int256 (x1W (zWord m)) ≤ 0) :
    ((posNegXNat m : Nat) : Int) =
      (-int256 (x1W (zWord m)) * lnPhaseScaleI) * (lnErrorBoundDen : Int) := by
  have hXn : (((-int256 (x1W (zWord m))).toNat : Nat) : Int) =
      -int256 (x1W (zWord m)) :=
    Int.toNat_of_nonneg (by omega)
  have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
  unfold posNegXNat
  simp only [Int.natCast_mul, hXn, hscale]

theorem posPhaseNatLt_cast {m c : Nat}
    (hX : int256 (x1W (zWord m)) ≤ 0)
    (hneg : posNegXNat m ≤ posConstNat c) :
    ((posPhaseNatLt m c : Nat) : Int) =
      posPhaseI m c * (lnErrorBoundDen : Int) := by
  have hconst := posConstNat_cast c
  have hnegc := posNegXNat_cast (m := m) hX
  have hsub : ((posConstNat c - posNegXNat m : Nat) : Int) =
      ((posConstNat c : Nat) : Int) - ((posNegXNat m : Nat) : Int) := by
    omega
  unfold posPhaseNatLt
  rw [hsub, hconst, hnegc]
  unfold posPhaseI
  rw [Int.add_mul, Int.add_mul, Int.add_mul]
  rw [show (-int256 (x1W (zWord m)) * lnPhaseScaleI) *
      (lnErrorBoundDen : Int) =
        -(int256 (x1W (zWord m)) * lnPhaseScaleI * (lnErrorBoundDen : Int)) by
        rw [Int.neg_mul, Int.neg_mul]]
  omega

theorem posPhaseNatGe_le_lnErrArg {m c : Nat} {r : Int}
    (hge : Sc ≤ m) (hmhi : m < MHI) (hc : c ≤ 160)
    (hr : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI < (r + 1) * 2 ^ 72)
    (hr0 : -1 ≤ r) :
    posPhaseNatGe m c ≤ lnErrArg r := by
  have hX := x1_nonneg_geF hge hmhi
  have hphase := posPhaseI_le_of_floor hc hr
  have hcore := c160_arg_le_int (A := posPhaseI m c) (r := r) hphase
  have harg : 0 ≤ r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
    have h0 : 0 ≤ r + 1 := by omega
    have hp : 0 ≤ (r + 1) * (1000000000 : Int) :=
      Int.mul_nonneg h0 (by decide)
    have e : (r + 1) * (1000000000 : Int) + 698600000 =
        r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
      unfold lnErrorBoundDen lnErrorBoundNum
      rw [Int.add_mul, Int.one_mul]
      omega
    rw [← e]
    exact Int.add_nonneg hp (by decide)
  apply Int.ofNat_le.mp
  rw [posPhaseNatGe_cast hX]
  unfold lnErrArg
  rw [Int.natCast_mul, Int.toNat_of_nonneg harg]
  have hnon : 0 ≤ 698600000 * twoPow99I := by
    unfold twoPow99I
    decide
  have hle := Int.le_trans (Int.le_add_of_nonneg_right hnon) hcore
  simpa [lnErrorBoundDen, lnErrorBoundNum, twoPow99I] using hle

theorem posNegXNat_le_posConstNat {m c : Nat}
    (hX : int256 (x1W (zWord m)) ≤ 0) (hc : c ≤ 160)
    (hV0 : 0 ≤ int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI) :
    posNegXNat m ≤ posConstNat c := by
  have hVs := v_scale_pos (int256 (x1W (zWord m))) c hc
  have hV0s : 0 ≤ posPhaseI m c := by
    have hmul := Int.mul_nonneg hV0
      (by unfold twoPow27I; decide : 0 ≤ twoPow27I)
    change 0 ≤ (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI) * twoPow27I at hmul
    have hVs' :
        (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
            lnBiasI) * twoPow27I =
          int256 (x1W (zWord m)) * lnPhaseScaleI +
            ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
              lnBiasI * twoPow27I := by
      simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
    rw [hVs'] at hmul
    simpa [posPhaseI, lnPhaseScaleI, twoPow27I, lnBiasI] using hmul
  apply Int.ofNat_le.mp
  rw [posNegXNat_cast hX, posConstNat_cast c]
  unfold posPhaseI at hV0s
  have hmain :
      -int256 (x1W (zWord m)) * lnPhaseScaleI ≤
        ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
          lnBiasI * twoPow27I := by
    rw [show -int256 (x1W (zWord m)) * lnPhaseScaleI =
        -(int256 (x1W (zWord m)) * lnPhaseScaleI) by rw [Int.neg_mul]]
    generalize int256 (x1W (zWord m)) * lnPhaseScaleI = A at hV0s ⊢
    omega
  exact Int.mul_le_mul_of_nonneg_right hmain (Int.natCast_nonneg _)

end LnFloorCert
