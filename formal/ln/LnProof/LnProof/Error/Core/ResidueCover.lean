import LnProof.Floor.CutEquiv
import LnProof.Error.Cert
import LnProof.Error.Core.CutDefs
import LnProof.Error.Core.Residue

/-!
# Error bound — ResidueCover

`PosShift*ResidueOk` predicates, `ResidueCell`, and the decidable residue cell-cover machinery.
-/

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

namespace LnFloorCert

open LnYul LnFloor Common.Exp Common.Poly

attribute [local irreducible] lnWadToRayBody


def PosShiftResidueOk (m c : Nat) (r : Int) : Prop :=
  posPhaseI m c * (lnErrorBoundDen : Int) + (lnErrorCoarsePosResidue : Int) ≤
    (r + 1) * twoPow99I * (lnErrorBoundDen : Int)

def PosShiftGeResidueOk (m c : Nat) (r : Int) : Prop :=
  posPhaseI m c * (lnErrorBoundDen : Int) + (lnErrorCoarseGePosResidue : Int) ≤
    (r + 1) * twoPow99I * (lnErrorBoundDen : Int)

def PosShiftResidueGapOk (m c : Nat) (r : Int) : Prop :=
  (lnErrorCoarsePosResidue : Int) ≤
    posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int)

def PosShiftGeResidueGapOk (m c : Nat) (r : Int) : Prop :=
  (lnErrorCoarseGePosResidue : Int) ≤
    posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int)

def PosShiftDirectResidueGapOk (m c : Nat) (r : Int) : Prop :=
  (lnErrorDirectResidueGap : Int) ≤ posResidueGap m c r

def residueGapOkB (m c : Nat) (r : Int) : Bool :=
  decide ((lnErrorCoarsePosResidue : Int) ≤
    posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int))

def geResidueGapOkB (m c : Nat) (r : Int) : Bool :=
  decide ((lnErrorCoarseGePosResidue : Int) ≤
    posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int))

def directResidueGapOkB (m c : Nat) (r : Int) : Bool :=
  decide ((lnErrorDirectResidueGap : Int) ≤ posResidueGap m c r)

def directResidueGapModOkB (m c : Nat) : Bool :=
  decide ((posAccI m c).toNat % twoPow72N ≤ twoPow72N - lnErrorDirectResidueGap)

theorem PosShiftResidueGapOk.of_bool {m c : Nat} {r : Int}
    (h : residueGapOkB m c r = true) : PosShiftResidueGapOk m c r := by
  unfold residueGapOkB PosShiftResidueGapOk at *
  exact of_decide_eq_true h

theorem PosShiftGeResidueGapOk.of_bool {m c : Nat} {r : Int}
    (h : geResidueGapOkB m c r = true) : PosShiftGeResidueGapOk m c r := by
  unfold geResidueGapOkB PosShiftGeResidueGapOk at *
  exact of_decide_eq_true h

theorem PosShiftDirectResidueGapOk.of_bool {m c : Nat} {r : Int}
    (h : directResidueGapOkB m c r = true) : PosShiftDirectResidueGapOk m c r := by
  unfold directResidueGapOkB PosShiftDirectResidueGapOk at *
  exact of_decide_eq_true h

theorem PosShiftDirectResidueGapOk.of_modB {m c : Nat}
    (hmlo : MLO ≤ m) (hmhi : m < MHI) (hc : c < 160)
    (h : directResidueGapModOkB m c = true) :
    PosShiftDirectResidueGapOk m c (int256 (lnTail (evmSub 160 c) m)) := by
  unfold directResidueGapModOkB at h
  have hmod :
      (posAccI m c).toNat % twoPow72N ≤ twoPow72N - lnErrorDirectResidueGap :=
    of_decide_eq_true h
  have heq := posResidueGap_eq_twoPow72_sub_mod (m := m) (c := c) hmlo hmhi hc
  change posResidueGap m c (int256 (lnTail (evmSub 160 c) m)) =
      ((twoPow72N - (posAccI m c).toNat % twoPow72N : Nat) : Int) at heq
  unfold PosShiftDirectResidueGapOk
  rw [heq]
  apply Int.ofNat_le.mpr
  have hgap_le_q : lnErrorDirectResidueGap ≤ twoPow72N := by
    unfold lnErrorDirectResidueGap twoPow72N
    decide
  omega

theorem PosShiftResidueGapOk_of_gap_threshold {m c : Nat} {r : Int}
    (hgap : posResidueGapThreshold ≤ posResidueGap m c r) :
    PosShiftResidueGapOk m c r := by
  have hconst :
      (lnErrorCoarsePosResidue : Int) ≤
        posResidueGapThreshold * twoPow27I * (lnErrorBoundDen : Int) := by
    unfold lnErrorCoarsePosResidue posResidueGapThreshold twoPow27I lnErrorBoundDen
    decide +kernel
  have h27 : 0 ≤ twoPow27I := by
    change (0 : Int) ≤ 134217728
    decide
  have hden : 0 ≤ (lnErrorBoundDen : Int) := by
    change (0 : Int) ≤ 1000000000
    decide
  have hmul := Int.mul_le_mul_of_nonneg_right hgap h27
  have hmul2 := Int.mul_le_mul_of_nonneg_right hmul hden
  unfold PosShiftResidueGapOk
  exact Int.le_trans hconst hmul2

theorem posResidueGap_lt_threshold_of_not_ok {m c : Nat} {r : Int}
    (_hgap_pos : 1 ≤ posResidueGap m c r)
    (h : residueGapOkB m c r = false) :
    posResidueGap m c r < posResidueGapThreshold := by
  unfold residueGapOkB at h
  rw [decide_eq_false_iff_not] at h
  by_cases hle : posResidueGapThreshold ≤ posResidueGap m c r
  · exact False.elim (h (PosShiftResidueGapOk_of_gap_threshold hle))
  · omega

theorem PosShiftResidueOk_of_gap {m c : Nat} {r : Int}
    (hc : c ≤ 160) (hgap : PosShiftResidueGapOk m c r) :
    PosShiftResidueOk m c r := by
  have hVs := v_scale_pos (int256 (x1W (zWord m))) c hc
  have hVs' : posAccI m c * twoPow27I = posPhaseI m c := by
    unfold posAccI posPhaseI
    simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
  unfold PosShiftResidueGapOk posResidueGap at hgap
  unfold PosShiftResidueOk
  rw [← hVs']
  unfold twoPow72I twoPow27I at hgap
  unfold twoPow27I twoPow99I
  have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
    unfold lnErrorBoundDen
    rfl
  rw [hden] at hgap ⊢
  omega

theorem PosShiftResidueOk_of_gapB {m c : Nat} {r : Int}
    (hc : c ≤ 160) (h : residueGapOkB m c r = true) :
    PosShiftResidueOk m c r :=
  PosShiftResidueOk_of_gap hc (PosShiftResidueGapOk.of_bool h)

theorem PosShiftGeResidueOk_of_gap {m c : Nat} {r : Int}
    (hc : c ≤ 160) (hgap : PosShiftGeResidueGapOk m c r) :
    PosShiftGeResidueOk m c r := by
  have hVs := v_scale_pos (int256 (x1W (zWord m))) c hc
  have hVs' : posAccI m c * twoPow27I = posPhaseI m c := by
    unfold posAccI posPhaseI
    simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
  unfold PosShiftGeResidueGapOk posResidueGap at hgap
  unfold PosShiftGeResidueOk
  rw [← hVs']
  unfold twoPow72I twoPow27I at hgap
  unfold twoPow27I twoPow99I
  have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
    unfold lnErrorBoundDen
    rfl
  rw [hden] at hgap ⊢
  omega

theorem PosShiftGeResidueOk_of_gapB {m c : Nat} {r : Int}
    (hc : c ≤ 160) (h : geResidueGapOkB m c r = true) :
    PosShiftGeResidueOk m c r :=
  PosShiftGeResidueOk_of_gap hc (PosShiftGeResidueGapOk.of_bool h)

structure ResidueCell where
  lo : Nat
  hi : Nat

def geResidueCellOkB (lo hi c : Nat) : Bool :=
  decide (Sc ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < MHI) &&
        decide (c < 160) &&
          decide (int256 (lnTail (evmSub 160 c) lo) =
            int256 (lnTail (evmSub 160 c) hi)) &&
            geResidueGapOkB hi c (int256 (lnTail (evmSub 160 c) hi))

def directResidueCellOkB (lo hi c : Nat) : Bool :=
  decide (MLO ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < MHI) &&
        decide (c < 160) &&
          decide (int256 (lnTail (evmSub 160 c) lo) =
            int256 (lnTail (evmSub 160 c) hi)) &&
            directResidueGapOkB hi c (int256 (lnTail (evmSub 160 c) hi))

def geResidueRunCellOkB (lo hi c : Nat) : Bool :=
  decide (Sc ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < MHI) &&
        decide (c < 160) &&
          let rlo := int256 (lnTail (evmSub 160 c) lo)
          decide (posAccI hi c < (rlo + 1) * twoPow72I) &&
            decide ((lnErrorCoarseGePosResidue : Int) ≤
              ((rlo + 1) * twoPow72I - posAccI hi c) * twoPow27I *
                (lnErrorBoundDen : Int))

def residueRunCellOkB (lo hi c : Nat) : Bool :=
  decide (MLO ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < MHI) &&
        decide (c < 160) &&
          let rlo := int256 (lnTail (evmSub 160 c) lo)
          decide (posAccI hi c < (rlo + 1) * twoPow72I) &&
            decide ((lnErrorCoarsePosResidue : Int) ≤
              ((rlo + 1) * twoPow72I - posAccI hi c) * twoPow27I *
                (lnErrorBoundDen : Int))

def directResidueRunCellOkB (lo hi c : Nat) : Bool :=
  decide (MLO ≤ lo) &&
    decide (lo ≤ hi) &&
      decide (hi < MHI) &&
        decide (c < 160) &&
          let rlo := int256 (lnTail (evmSub 160 c) lo)
          decide (posAccI hi c < (rlo + 1) * twoPow72I) &&
            decide ((lnErrorDirectResidueGap : Int) ≤
              (rlo + 1) * twoPow72I - posAccI hi c)

theorem geResidueCellOkB_sound {lo hi m c : Nat}
    (h : geResidueCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGeResidueOk m c (int256 (lnTail (evmSub 160 c) m)) := by
  unfold geResidueCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hloSc, _hlohi⟩, hhi⟩, hc⟩, htailEq⟩, hgapHiB⟩ := h
  have hloMLO : MLO ≤ lo := by
    simp only [Sc, MLO] at hloSc ⊢
    omega
  have hgapLe :=
    posResidueGap_ge_of_same_posAcc_endpoints hloMLO hlom hmhi hhi hc htailEq
  have hgapHi := PosShiftGeResidueGapOk.of_bool hgapHiB
  have hgapM :
      PosShiftGeResidueGapOk m c (int256 (lnTail (evmSub 160 c) m)) := by
    unfold PosShiftGeResidueGapOk at hgapHi ⊢
    have h27 : 0 ≤ twoPow27I := by
      change (0 : Int) ≤ 134217728
      decide
    have hden : 0 ≤ (lnErrorBoundDen : Int) := by
      change (0 : Int) ≤ 1000000000
      decide
    have hmul := Int.mul_le_mul_of_nonneg_right hgapLe h27
    have hmul2 := Int.mul_le_mul_of_nonneg_right hmul hden
    exact Int.le_trans hgapHi hmul2
  exact PosShiftGeResidueOk_of_gap (by omega : c ≤ 160) hgapM

theorem directResidueCellOkB_sound {lo hi m c : Nat}
    (h : directResidueCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftDirectResidueGapOk m c (int256 (lnTail (evmSub 160 c) m)) := by
  unfold directResidueCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hlo, _hlohi⟩, hhi⟩, hc⟩, htailEq⟩, hgapHiB⟩ := h
  have hgapLe :=
    posResidueGap_ge_of_same_posAcc_endpoints hlo hlom hmhi hhi hc htailEq
  have hgapHi := PosShiftDirectResidueGapOk.of_bool hgapHiB
  unfold PosShiftDirectResidueGapOk at hgapHi ⊢
  exact Int.le_trans hgapHi hgapLe

theorem lnTail_eq_of_residue_run {lo hi m c : Nat}
    (hlo : MLO ≤ lo) (hlom : lo ≤ m) (hmhi : m ≤ hi) (hhi : hi < MHI)
    (hc : c < 160)
    (hboundary : posAccI hi c <
      (int256 (lnTail (evmSub 160 c) lo) + 1) * twoPow72I) :
    int256 (lnTail (evmSub 160 c) m) =
      int256 (lnTail (evmSub 160 c) lo) := by
  have hlohi : lo < MHI := by omega
  have hmhi' : m < MHI := by omega
  have hbrLo := lnTail_floor_bracket_pos hlo hlohi hc
  have hbrM := lnTail_floor_bracket_pos (by omega : MLO ≤ m) hmhi' hc
  have haccLoM := posAccI_mono_m (c := c) hlo hlom hmhi'
  have haccMHi := posAccI_mono_m (c := c) (by omega : MLO ≤ m) hmhi hhi
  let rlo := int256 (lnTail (evmSub 160 c) lo)
  let rm := int256 (lnTail (evmSub 160 c) m)
  have hboundaryM : posAccI m c < (rlo + 1) * twoPow72I := by
    exact Int.lt_of_le_of_lt haccMHi (by simpa [rlo] using hboundary)
  have hrm_le : rm ≤ rlo := by
    have hmul : rm * twoPow72I < (rlo + 1) * twoPow72I :=
      Int.lt_of_le_of_lt hbrM.1 hboundaryM
    have hlt : rm < rlo + 1 :=
      (Int.mul_lt_mul_right (a := twoPow72I) (b := rm) (c := rlo + 1)
        (by unfold twoPow72I; decide)).mp hmul
    exact Int.le_of_lt_add_one hlt
  have hrlo_le : rlo ≤ rm := by
    have hmul : rlo * twoPow72I < (rm + 1) * twoPow72I := by
      exact Int.lt_of_le_of_lt (Int.le_trans hbrLo.1 haccLoM) hbrM.2
    have hlt : rlo < rm + 1 :=
      (Int.mul_lt_mul_right (a := twoPow72I) (b := rlo) (c := rm + 1)
        (by unfold twoPow72I; decide)).mp hmul
    exact Int.le_of_lt_add_one hlt
  exact Int.le_antisymm hrm_le hrlo_le

theorem geResidueRunCellOkB_sound {lo hi m c : Nat}
    (h : geResidueRunCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGeResidueOk m c (int256 (lnTail (evmSub 160 c) m)) := by
  unfold geResidueRunCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hloSc, _hlohi⟩, hhi⟩, hc⟩, hrun⟩ := h
  obtain ⟨hboundary, hgapHi⟩ := hrun
  have hlo : MLO ≤ lo := by
    simp only [Sc, MLO] at hloSc ⊢
    omega
  have htail := lnTail_eq_of_residue_run hlo hlom hmhi hhi hc hboundary
  have hmhi' : m < MHI := by omega
  have haccMHi := posAccI_mono_m (c := c) (by omega : MLO ≤ m) hmhi hhi
  let rlo := int256 (lnTail (evmSub 160 c) lo)
  let rm := int256 (lnTail (evmSub 160 c) m)
  have hgapLe :
      (rlo + 1) * twoPow72I - posAccI hi c ≤
        (rm + 1) * twoPow72I - posAccI m c := by
    rw [show rm = rlo by simpa [rm, rlo] using htail]
    exact Int.sub_le_sub_left haccMHi ((rlo + 1) * twoPow72I)
  have h27 : 0 ≤ twoPow27I := by
    unfold twoPow27I
    decide
  have hden : 0 ≤ (lnErrorBoundDen : Int) := by
    change (0 : Int) ≤ 1000000000
    decide
  have hscaled1 :
      ((rlo + 1) * twoPow72I - posAccI hi c) * twoPow27I ≤
        ((rm + 1) * twoPow72I - posAccI m c) * twoPow27I :=
    Int.mul_le_mul_of_nonneg_right hgapLe h27
  have hscaled2 :
      ((rlo + 1) * twoPow72I - posAccI hi c) * twoPow27I *
          (lnErrorBoundDen : Int) ≤
        ((rm + 1) * twoPow72I - posAccI m c) * twoPow27I *
          (lnErrorBoundDen : Int) :=
    Int.mul_le_mul_of_nonneg_right hscaled1 hden
  have hgapM : PosShiftGeResidueGapOk m c rm := by
    unfold PosShiftGeResidueGapOk posResidueGap
    exact Int.le_trans hgapHi hscaled2
  simpa [rm] using PosShiftGeResidueOk_of_gap (by omega : c ≤ 160) hgapM

theorem residueRunCellOkB_sound {lo hi m c : Nat}
    (h : residueRunCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftResidueOk m c (int256 (lnTail (evmSub 160 c) m)) := by
  unfold residueRunCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, _hlohi⟩, hhi⟩, hc⟩, hrun⟩ := h
  obtain ⟨hboundary, hgapHi⟩ := hrun
  have htail := lnTail_eq_of_residue_run hlo hlom hmhi hhi hc hboundary
  have haccMHi := posAccI_mono_m (c := c) (by omega : MLO ≤ m) hmhi hhi
  let rlo := int256 (lnTail (evmSub 160 c) lo)
  let rm := int256 (lnTail (evmSub 160 c) m)
  have hgapLe :
      (rlo + 1) * twoPow72I - posAccI hi c ≤
        (rm + 1) * twoPow72I - posAccI m c := by
    rw [show rm = rlo by simpa [rm, rlo] using htail]
    exact Int.sub_le_sub_left haccMHi ((rlo + 1) * twoPow72I)
  have h27 : 0 ≤ twoPow27I := by
    unfold twoPow27I
    decide
  have hden : 0 ≤ (lnErrorBoundDen : Int) := by
    change (0 : Int) ≤ 1000000000
    decide
  have hscaled1 :
      ((rlo + 1) * twoPow72I - posAccI hi c) * twoPow27I ≤
        ((rm + 1) * twoPow72I - posAccI m c) * twoPow27I :=
    Int.mul_le_mul_of_nonneg_right hgapLe h27
  have hscaled2 :
      ((rlo + 1) * twoPow72I - posAccI hi c) * twoPow27I *
          (lnErrorBoundDen : Int) ≤
        ((rm + 1) * twoPow72I - posAccI m c) * twoPow27I *
          (lnErrorBoundDen : Int) :=
    Int.mul_le_mul_of_nonneg_right hscaled1 hden
  have hgapM : PosShiftResidueGapOk m c rm := by
    unfold PosShiftResidueGapOk posResidueGap
    exact Int.le_trans hgapHi hscaled2
  simpa [rm] using PosShiftResidueOk_of_gap (by omega : c ≤ 160) hgapM

theorem directResidueRunCellOkB_sound {lo hi m c : Nat}
    (h : directResidueRunCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftDirectResidueGapOk m c (int256 (lnTail (evmSub 160 c) m)) := by
  unfold directResidueRunCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, _hlohi⟩, hhi⟩, hc⟩, hrun⟩ := h
  obtain ⟨hboundary, hgapHi⟩ := hrun
  have htail := lnTail_eq_of_residue_run hlo hlom hmhi hhi hc hboundary
  have haccMHi := posAccI_mono_m (c := c) (by omega : MLO ≤ m) hmhi hhi
  let rlo := int256 (lnTail (evmSub 160 c) lo)
  let rm := int256 (lnTail (evmSub 160 c) m)
  have hgapLe :
      (rlo + 1) * twoPow72I - posAccI hi c ≤
        (rm + 1) * twoPow72I - posAccI m c := by
    rw [show rm = rlo by simpa [rm, rlo] using htail]
    exact Int.sub_le_sub_left haccMHi ((rlo + 1) * twoPow72I)
  have hgapM : PosShiftDirectResidueGapOk m c rm := by
    unfold PosShiftDirectResidueGapOk posResidueGap
    exact Int.le_trans hgapHi hgapLe
  simpa [rm] using hgapM

def geResidueCellListCoverB (c : Nat) : Nat → Nat → List ResidueCell → Bool
  | lo, hi, [] => decide (hi < lo)
  | lo, hi, cell :: cells =>
      decide (cell.lo = lo) &&
        decide (lo ≤ cell.hi) &&
          decide (cell.hi ≤ hi) &&
            geResidueCellOkB cell.lo cell.hi c &&
              geResidueCellListCoverB c (cell.hi + 1) hi cells

theorem geResidueCellListCoverB_sound {cells : List ResidueCell} {c lo hi m : Nat}
    (h : geResidueCellListCoverB c lo hi cells = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGeResidueOk m c (int256 (lnTail (evmSub 160 c) m)) := by
  induction cells generalizing lo with
  | nil =>
      unfold geResidueCellListCoverB at h
      have hlt : hi < lo := of_decide_eq_true h
      omega
  | cons cell cells ih =>
      unfold geResidueCellListCoverB at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hlo, _hlohi⟩, _hhihi⟩, hok⟩, hrest⟩ := h
      by_cases hmcell : m ≤ cell.hi
      · exact geResidueCellOkB_sound hok (by omega) hmcell
      · exact ih hrest (by omega)

def directResidueCellListCoverB (c : Nat) : Nat → Nat → List ResidueCell → Bool
  | lo, hi, [] => decide (hi < lo)
  | lo, hi, cell :: cells =>
      decide (cell.lo = lo) &&
        decide (lo ≤ cell.hi) &&
          decide (cell.hi ≤ hi) &&
            directResidueCellOkB cell.lo cell.hi c &&
              directResidueCellListCoverB c (cell.hi + 1) hi cells

theorem directResidueCellListCoverB_sound {cells : List ResidueCell} {c lo hi m : Nat}
    (h : directResidueCellListCoverB c lo hi cells = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftDirectResidueGapOk m c (int256 (lnTail (evmSub 160 c) m)) := by
  induction cells generalizing lo with
  | nil =>
      unfold directResidueCellListCoverB at h
      have hlt : hi < lo := of_decide_eq_true h
      omega
  | cons cell cells ih =>
      unfold directResidueCellListCoverB at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hlo, _hlohi⟩, _hhihi⟩, hok⟩, hrest⟩ := h
      by_cases hmcell : m ≤ cell.hi
      · exact directResidueCellOkB_sound hok (by omega) hmcell
      · exact ih hrest (by omega)

theorem pos_direct_residue_arg_le_int {A r : Int}
    (hres : A * (lnErrorBoundDen : Int) +
        (lnErrorDirectResidueGap : Int) * twoPow27I * (lnErrorBoundDen : Int) ≤
      (r + 1) * twoPow99I * (lnErrorBoundDen : Int)) :
    A * (lnErrorBoundDen : Int) + (lnErrorExtraNum : Int) * twoPow99I +
        (lnErrorDirectResidueGap : Int) * twoPow27I * (lnErrorBoundDen : Int) ≤
      (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) * twoPow99I := by
  have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
    unfold lnErrorBoundDen
    rfl
  have hnum : ((lnErrorBoundNum : Nat) : Int) = (1698600000 : Int) := by
    unfold lnErrorBoundNum
    rfl
  have hextra : ((lnErrorExtraNum : Nat) : Int) = (698600000 : Int) := by
    unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen
    decide +kernel
  rw [hden] at hres
  rw [hden, hnum, hextra]
  unfold twoPow99I twoPow27I at hres ⊢
  omega

theorem direct_residue_phase_bound {m c : Nat} {r : Int}
    (hc : c ≤ 160) (hgap : PosShiftDirectResidueGapOk m c r) :
    posPhaseI m c * (lnErrorBoundDen : Int) +
        (lnErrorDirectResidueGap : Int) * twoPow27I * (lnErrorBoundDen : Int) ≤
      (r + 1) * twoPow99I * (lnErrorBoundDen : Int) := by
  have hVs := v_scale_pos (int256 (x1W (zWord m))) c hc
  have hVs' : posAccI m c * twoPow27I = posPhaseI m c := by
    unfold posAccI posPhaseI
    simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
  unfold PosShiftDirectResidueGapOk posResidueGap at hgap
  rw [← hVs']
  unfold twoPow27I twoPow99I
  unfold twoPow72I at hgap
  have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
    unfold lnErrorBoundDen
    rfl
  rw [hden]
  omega

end LnFloorCert
