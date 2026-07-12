import LnProof.Floor.CutEquiv
import LnProof.Error.Cert
import LnProof.Error.Core.CutDefs
import LnProof.Error.Core.ExpMargin
import LnProof.Error.Core.ResidueCover
import LnProof.Error.Core.Budget
import LnProof.Error.Core.Direct
import LnProof.Error.Core.PhaseCover
import LnProof.Error.Core.Bounds
import LnProof.Error.Core.Assembly
import LnProof.Cert.HardMantissaLtGap

/-!
# Error bound — BranchCert

Branch-certificate predicates, the decidable cell/cover deciders, and the `lnWadToRayBody_positive_shift_*_branch_cert` theorems.
-/

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

namespace LnFloorCert

open LnYul LnFloor Common.Exp Common.Poly

attribute [local irreducible] lnWadToRayBody


def PosShiftGeBranchCert (m c : Nat) (r : Int) : Prop :=
  PosShiftGeResidueOk m c r ∨
    PosShiftGeTopBudgetIneqOk m c ∨
      PosShiftTopDirectOk 320 m c ∨
        PosShiftGePhaseDirectOk 320 m c ∨
          (PosShiftDirectResidueGapOk m c r ∧ PosShiftGePhaseGapDirectOk 320 m c)

def PosShiftLtBranchCert (m c : Nat) (r : Int) : Prop :=
  PosShiftResidueOk m c r ∨
    PosShiftLtTopBudgetIneqOk m c ∨
      PosShiftTopDirectOk 320 m c ∨
        PosShiftLtPhaseDirectOk 320 m c ∨
          (PosShiftDirectResidueGapOk m c r ∧ PosShiftLtPhaseGapDirectOk 320 m c)

def posShiftGeTopBudgetIneqOkB (m c : Nat) : Bool :=
  decide (wadRayNum (posTopX c m) * (posBaseWGe c * lnErrQ) ≤
    (posBaseYGe m c *
      (lnErrQ + posAvailGe m c (int256 (lnTail (evmSub 160 c) m)))) *
        wadRayStrictDen)

def posShiftLtTopBudgetIneqOkB (m c : Nat) : Bool :=
  decide (wadRayNum (posTopX c m) * (posBaseWLt c * lnErrQ) ≤
    (posBaseYLt m c *
      (lnErrQ + posAvailLt m c (int256 (lnTail (evmSub 160 c) m)))) *
        wadRayStrictDen)

def posShiftTopDirectOkB (m c : Nat) : Bool :=
  sumGEB 320 (lnErrArg (int256 (lnTail (evmSub 160 c) m))) lnErrQ
    (posTopX c m) (10 ^ 18)

def posShiftGePhaseDirectOkB (m c : Nat) : Bool :=
  sumGEB 320 (posPhaseNatGe m c + lnPhaseExtraArg) lnErrQ
    (posTopX c m) (10 ^ 18)

def posShiftLtPhaseDirectOkB (m c : Nat) : Bool :=
  sumGEB 320 (posPhaseNatLt m c + lnPhaseExtraArg) lnErrQ
    (posTopX c m) (10 ^ 18)

def posShiftGeMinPhaseDirectOkB (m c : Nat) : Bool :=
  sumGEB 320 (posPhaseNatGe m c + minPosAvail) lnErrQ
    (posTopX c m) (10 ^ 18)

def posShiftLtMinPhaseDirectOkB (m c : Nat) : Bool :=
  sumGEB 320 (posPhaseNatLt m c + minPosAvail) lnErrQ
    (posTopX c m) (10 ^ 18)

def posShiftGePhaseGapDirectOkB (m c : Nat) : Bool :=
  sumGEB 320 (posPhaseNatGe m c + lnPhaseExtraArg + lnDirectGapArg) lnErrQ
    (posTopX c m) (10 ^ 18)

def posShiftGeBranchCertB (m c : Nat) (r : Int) : Bool :=
  geResidueGapOkB m c r ||
    (posShiftGeTopBudgetIneqOkB m c ||
      (posShiftTopDirectOkB m c ||
        (posShiftGePhaseDirectOkB m c ||
          (directResidueGapOkB m c r && posShiftGePhaseGapDirectOkB m c)
        )))

def posShiftLtBranchCertB (m c : Nat) (r : Int) : Bool :=
  residueGapOkB m c r ||
    (posShiftLtTopBudgetIneqOkB m c ||
      (posShiftTopDirectOkB m c ||
        (posShiftLtPhaseDirectOkB m c ||
          (directResidueGapOkB m c r && posShiftLtPhaseGapDirectOkB m c)
        )))

theorem hardMantissaLtGapBranch {c : Nat} (hc1 : 1 ≤ c) (hc : c < 160) :
    PosShiftDirectResidueGapOk lnErrorHardMantissa c
        (int256 (lnTail (evmSub 160 c) lnErrorHardMantissa)) ∧
      PosShiftLtPhaseGapDirectOk 320 lnErrorHardMantissa c := by
  have h := List.all_eq_true.mp hardMantissaLtGapBranch_all (c - 1)
    (List.mem_range.mpr (by omega : c - 1 < 159))
  rw [show c - 1 + 1 = c by omega] at h
  unfold hardMantissaLtGapBranchB at h
  rw [Bool.and_eq_true] at h
  exact ⟨PosShiftDirectResidueGapOk.of_bool h.1, by
    unfold posShiftLtPhaseGapDirectOkB at h
    unfold PosShiftLtPhaseGapDirectOk
    exact sumGE_of_sumGEB h.2⟩

theorem hardMantissaLtBranchCert {c : Nat} (hc1 : 1 ≤ c) (hc : c < 160) :
    PosShiftLtBranchCert lnErrorHardMantissa c
      (int256 (lnTail (evmSub 160 c) lnErrorHardMantissa)) := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (hardMantissaLtGapBranch hc1 hc))))

theorem posShiftGeBranchCert_of_bool {m c : Nat} {r : Int} (hc : c ≤ 160)
    (h : posShiftGeBranchCertB m c r = true) :
    PosShiftGeBranchCert m c r := by
  unfold posShiftGeBranchCertB at h
  unfold PosShiftGeBranchCert
  rw [Bool.or_eq_true] at h
  rcases h with hres | hrest
  · exact Or.inl (PosShiftGeResidueOk_of_gapB hc hres)
  · rw [Bool.or_eq_true] at hrest
    rcases hrest with htop | hrest
    · exact Or.inr (Or.inl (by
      unfold posShiftGeTopBudgetIneqOkB at htop
      unfold PosShiftGeTopBudgetIneqOk PosShiftGeBudgetIneqOk
      exact of_decide_eq_true htop))
    · rw [Bool.or_eq_true] at hrest
      rcases hrest with hdir | hrest
      · exact Or.inr (Or.inr (Or.inl (by
        unfold posShiftTopDirectOkB at hdir
        unfold PosShiftTopDirectOk
        exact sumGE_of_sumGEB hdir)))
      · rw [Bool.or_eq_true] at hrest
        rcases hrest with hphase | hgapBool
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by
        unfold posShiftGePhaseDirectOkB at hphase
        unfold PosShiftGePhaseDirectOk
        exact sumGE_of_sumGEB hphase))))
        · rw [Bool.and_eq_true] at hgapBool
          have hgap := hgapBool
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨PosShiftDirectResidueGapOk.of_bool hgap.1, by
        unfold posShiftGePhaseGapDirectOkB at hgap
        unfold PosShiftGePhaseGapDirectOk
        exact sumGE_of_sumGEB hgap.2⟩)))

theorem posShiftLtBranchCert_of_bool {m c : Nat} {r : Int}
    (hc : c ≤ 160)
    (h : posShiftLtBranchCertB m c r = true) :
    PosShiftLtBranchCert m c r := by
  unfold posShiftLtBranchCertB at h
  unfold PosShiftLtBranchCert
  rw [Bool.or_eq_true] at h
  rcases h with hres | hrest
  · exact Or.inl (PosShiftResidueOk_of_gapB hc hres)
  · rw [Bool.or_eq_true] at hrest
    rcases hrest with htop | hrest
    · exact Or.inr (Or.inl (by
      unfold posShiftLtTopBudgetIneqOkB at htop
      unfold PosShiftLtTopBudgetIneqOk PosShiftLtBudgetIneqOk
      exact of_decide_eq_true htop))
    · rw [Bool.or_eq_true] at hrest
      rcases hrest with hdir | hrest
      · exact Or.inr (Or.inr (Or.inl (by
        unfold posShiftTopDirectOkB at hdir
        unfold PosShiftTopDirectOk
        exact sumGE_of_sumGEB hdir)))
      · rw [Bool.or_eq_true] at hrest
        rcases hrest with hphase | hgapBool
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by
        unfold posShiftLtPhaseDirectOkB at hphase
        unfold PosShiftLtPhaseDirectOk
        exact sumGE_of_sumGEB hphase))))
        · rw [Bool.and_eq_true] at hgapBool
          have hgap := hgapBool
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨PosShiftDirectResidueGapOk.of_bool hgap.1, by
        unfold posShiftLtPhaseGapDirectOkB at hgap
        unfold PosShiftLtPhaseGapDirectOk
        exact sumGE_of_sumGEB hgap.2⟩)))

def directTopCellOkB (lo hi c : Nat) : Bool :=
  ({ c := c, lo := lo, hi := hi, n := 320 } : PosShiftDirectCell).okB

def geBranchCellOkB (lo hi c : Nat) : Bool :=
  geResidueRunCellOkB lo hi c ||
    (geResidueCellOkB lo hi c ||
      (geTopBudgetCoarseCellOkB lo hi c ||
        (geTopBudgetRunCellOkB lo hi c ||
          (directTopCellOkB lo hi c ||
            (gePhaseCellOkB lo hi c ||
              ((directResidueRunCellOkB lo hi c && gePhaseGapCellOkB lo hi c) ||
                (directResidueCellOkB lo hi c && gePhaseGapCellOkB lo hi c)))))))

def ltBranchCellOkB (lo hi c : Nat) : Bool :=
  residueRunCellOkB lo hi c ||
    (ltTopBudgetCoarseCellOkB lo hi c ||
      (ltTopBudgetRunCellOkB lo hi c ||
        (directTopCellOkB lo hi c ||
          (ltPhaseCellOkB lo hi c ||
            ((directResidueRunCellOkB lo hi c && ltPhaseGapCellOkB lo hi c) ||
              (directResidueCellOkB lo hi c && ltPhaseGapCellOkB lo hi c))))))

theorem geBranchCellOkB_sound {lo hi m c : Nat}
    (h : geBranchCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGeBranchCert m c (int256 (lnTail (evmSub 160 c) m)) := by
  unfold geBranchCellOkB at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with hrun | hrest
  · exact Or.inl (geResidueRunCellOkB_sound hrun hlom hmhi)
  rcases hrest with hres | hrest
  · exact Or.inl (geResidueCellOkB_sound hres hlom hmhi)
  rcases hrest with htop | hrest
  · exact Or.inr (Or.inl (geTopBudgetCoarseCellOkB_sound htop hlom hmhi))
  rcases hrest with htop | hrest
  · exact Or.inr (Or.inl (geTopBudgetRunCellOkB_sound htop hlom hmhi))
  rcases hrest with hdir | hrest
  · exact Or.inr (Or.inr (Or.inl
      (PosShiftDirectCell.sound (PosShiftDirectCell.ok_of_okB hdir)
        (by
          unfold PosShiftDirectCell.Covers directTopCellOkB at *
          exact ⟨rfl, hlom, hmhi⟩))))
  rcases hrest with hphase | hgap
  · exact Or.inr (Or.inr (Or.inr (Or.inl (gePhaseCell_sound hphase hlom hmhi))))
  · rcases hgap with hgapRun | hgapCell
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨directResidueRunCellOkB_sound hgapRun.1 hlom hmhi,
          gePhaseGapCell_sound hgapRun.2 hlom hmhi⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨directResidueCellOkB_sound hgapCell.1 hlom hmhi,
          gePhaseGapCell_sound hgapCell.2 hlom hmhi⟩)))

theorem ltBranchCellOkB_sound {lo hi m c : Nat}
    (h : ltBranchCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftLtBranchCert m c (int256 (lnTail (evmSub 160 c) m)) := by
  unfold ltBranchCellOkB at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with hres | hrest
  · exact Or.inl (residueRunCellOkB_sound hres hlom hmhi)
  rcases hrest with htop | hrest
  · exact Or.inr (Or.inl (ltTopBudgetCoarseCellOkB_sound htop hlom hmhi))
  rcases hrest with htop | hrest
  · exact Or.inr (Or.inl (ltTopBudgetRunCellOkB_sound htop hlom hmhi))
  rcases hrest with hdir | hrest
  · exact Or.inr (Or.inr (Or.inl
      (PosShiftDirectCell.sound (PosShiftDirectCell.ok_of_okB hdir)
        (by
          unfold PosShiftDirectCell.Covers directTopCellOkB at *
          exact ⟨rfl, hlom, hmhi⟩))))
  rcases hrest with hphase | hgap
  · exact Or.inr (Or.inr (Or.inr (Or.inl (ltPhaseCell_sound hphase hlom hmhi))))
  · rcases hgap with hgapRun | hgapCell
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨directResidueRunCellOkB_sound hgapRun.1 hlom hmhi,
          ltPhaseGapCell_sound hgapRun.2 hlom hmhi⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨directResidueCellOkB_sound hgapCell.1 hlom hmhi,
          ltPhaseGapCell_sound hgapCell.2 hlom hmhi⟩)))

def geBranchCellListCoverB (c : Nat) : Nat → Nat → List ResidueCell → Bool
  | lo, hi, [] => decide (hi < lo)
  | lo, hi, cell :: cells =>
      decide (cell.lo = lo) &&
        decide (lo ≤ cell.hi) &&
          decide (cell.hi ≤ hi) &&
            geBranchCellOkB cell.lo cell.hi c &&
              geBranchCellListCoverB c (cell.hi + 1) hi cells

def ltBranchCellListCoverB (c : Nat) : Nat → Nat → List ResidueCell → Bool
  | lo, hi, [] => decide (hi < lo)
  | lo, hi, cell :: cells =>
      decide (cell.lo = lo) &&
        decide (lo ≤ cell.hi) &&
          decide (cell.hi ≤ hi) &&
            ltBranchCellOkB cell.lo cell.hi c &&
              ltBranchCellListCoverB c (cell.hi + 1) hi cells

theorem geBranchCellListCoverB_sound {cells : List ResidueCell} {c lo hi m : Nat}
    (h : geBranchCellListCoverB c lo hi cells = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGeBranchCert m c (int256 (lnTail (evmSub 160 c) m)) := by
  induction cells generalizing lo with
  | nil =>
      unfold geBranchCellListCoverB at h
      have hlt : hi < lo := of_decide_eq_true h
      omega
  | cons cell cells ih =>
      unfold geBranchCellListCoverB at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hlo, _hlohi⟩, _hhihi⟩, hok⟩, hrest⟩ := h
      by_cases hmcell : m ≤ cell.hi
      · exact geBranchCellOkB_sound hok (by omega) hmcell
      · exact ih hrest (by omega)

theorem ltBranchCellListCoverB_sound {cells : List ResidueCell} {c lo hi m : Nat}
    (h : ltBranchCellListCoverB c lo hi cells = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftLtBranchCert m c (int256 (lnTail (evmSub 160 c) m)) := by
  induction cells generalizing lo with
  | nil =>
      unfold ltBranchCellListCoverB at h
      have hlt : hi < lo := of_decide_eq_true h
      omega
  | cons cell cells ih =>
      unfold ltBranchCellListCoverB at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hlo, _hlohi⟩, _hhihi⟩, hok⟩, hrest⟩ := h
      by_cases hmcell : m ≤ cell.hi
      · exact ltBranchCellOkB_sound hok (by omega) hmcell
      · exact ih hrest (by omega)

def geBranchCoverB : Nat → Nat → Nat → Nat → Bool
  | 0, _c, lo, hi => decide (hi < lo)
  | fuel + 1, c, lo, hi =>
      if hi < lo then
        true
      else
        let mx := phaseSearchMax phaseSearchFuel (fun h => geBranchCellOkB lo h c)
          lo hi (lo - 1)
        decide (lo ≤ mx) &&
          decide (mx ≤ hi) &&
            geBranchCellOkB lo mx c &&
              geBranchCoverB fuel c (mx + 1) hi

def ltBranchCoverB : Nat → Nat → Nat → Nat → Bool
  | 0, _c, lo, hi => decide (hi < lo)
  | fuel + 1, c, lo, hi =>
      if hi < lo then
        true
      else
        let mx := phaseSearchMax phaseSearchFuel (fun h => ltBranchCellOkB lo h c)
          lo hi (lo - 1)
        decide (lo ≤ mx) &&
          decide (mx ≤ hi) &&
            ltBranchCellOkB lo mx c &&
              ltBranchCoverB fuel c (mx + 1) hi

theorem geBranchCoverB_sound {fuel c lo hi m : Nat}
    (h : geBranchCoverB fuel c lo hi = true) (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGeBranchCert m c (int256 (lnTail (evmSub 160 c) m)) := by
  revert lo
  induction fuel with
  | zero =>
      intro lo h hlom
      unfold geBranchCoverB at h
      simp only [decide_eq_true_eq] at h
      omega
  | succ fuel ih =>
      intro lo h hlom
      unfold geBranchCoverB at h
      by_cases hdone : hi < lo
      · rw [if_pos hdone] at h
        omega
      · rw [if_neg hdone] at h
        let mx := phaseSearchMax phaseSearchFuel (fun h => geBranchCellOkB lo h c)
          lo hi (lo - 1)
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨hlmx, hmxhi⟩, hcell⟩, hrest⟩ := h
        by_cases hleft : m ≤ mx
        · exact geBranchCellOkB_sound hcell hlom hleft
        · exact ih (lo := mx + 1) hrest (by omega)

theorem ltBranchCoverB_sound {fuel c lo hi m : Nat}
    (h : ltBranchCoverB fuel c lo hi = true) (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftLtBranchCert m c (int256 (lnTail (evmSub 160 c) m)) := by
  revert lo
  induction fuel with
  | zero =>
      intro lo h hlom
      unfold ltBranchCoverB at h
      simp only [decide_eq_true_eq] at h
      omega
  | succ fuel ih =>
      intro lo h hlom
      unfold ltBranchCoverB at h
      by_cases hdone : hi < lo
      · rw [if_pos hdone] at h
        omega
      · rw [if_neg hdone] at h
        let mx := phaseSearchMax phaseSearchFuel (fun h => ltBranchCellOkB lo h c)
          lo hi (lo - 1)
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨hlmx, hmxhi⟩, hcell⟩, hrest⟩ := h
        by_cases hleft : m ≤ mx
        · exact ltBranchCellOkB_sound hcell hlom hleft
        · exact ih (lo := mx + 1) hrest (by omega)

def branchCoverFuel : Nat := 1024

def phaseYMax (n p q w : Nat) : Nat :=
  let s := expSumState p q n
  s.1 * w / s.2.1

def phaseTopMaxHi (n p q w c hi : Nat) : Nat :=
  min hi (((phaseYMax n p q w + 1) / 2 ^ (160 - c)) - 1)

def ltPhaseTopMaxHi (n p q w c lo hi : Nat) : Nat :=
  let mx := phaseTopMaxHi n p q w c hi
  if lo < lnErrorHardMantissa ∧ lnErrorHardMantissa ≤ mx then
    lnErrorHardMantissa - 1
  else
    mx

def gePhaseCoverFastB : Nat → Nat → Nat → Nat → Bool
  | 0, _c, lo, hi => decide (hi < lo)
  | fuel + 1, c, lo, hi =>
      if hi < lo then
        true
      else
        let mx := phaseTopMaxHi 320 (posPhaseNatGe lo c + lnPhaseExtraArg)
          lnErrQ (10 ^ 18) c hi
        decide (lo ≤ mx) &&
          gePhaseCellOkB lo mx c &&
            gePhaseCoverFastB fuel c (mx + 1) hi

def ltPhaseCoverFastB : Nat → Nat → Nat → Nat → Bool
  | 0, _c, lo, hi => decide (hi < lo)
  | fuel + 1, c, lo, hi =>
      if hi < lo then
        true
      else if lo = lnErrorHardMantissa then
        ltPhaseCoverFastB fuel c (lo + 1) hi
      else
        let mx := ltPhaseTopMaxHi 320 (posPhaseNatLt lo c + lnPhaseExtraArg)
          lnErrQ (10 ^ 18) c lo hi
        decide (lo ≤ mx) &&
          ltPhaseCellOkB lo mx c &&
            ltPhaseCoverFastB fuel c (mx + 1) hi

theorem gePhaseCoverFastB_sound {fuel c lo hi m : Nat}
    (h : gePhaseCoverFastB fuel c lo hi = true) (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGePhaseDirectOk 320 m c := by
  revert lo
  induction fuel with
  | zero =>
      intro lo h hlom
      unfold gePhaseCoverFastB at h
      simp only [decide_eq_true_eq] at h
      omega
  | succ fuel ih =>
      intro lo h hlom
      unfold gePhaseCoverFastB at h
      by_cases hdone : hi < lo
      · rw [if_pos hdone] at h
        omega
      · rw [if_neg hdone] at h
        let mx := phaseTopMaxHi 320 (posPhaseNatGe lo c + lnPhaseExtraArg)
          lnErrQ (10 ^ 18) c hi
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨hlmx, hcell⟩, hrest⟩ := h
        by_cases hleft : m ≤ mx
        · exact gePhaseCell_sound hcell hlom hleft
        · exact ih (lo := mx + 1) hrest (by omega)

theorem ltPhaseCoverFastB_sound {fuel c lo hi m : Nat}
    (h : ltPhaseCoverFastB fuel c lo hi = true) (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    m = lnErrorHardMantissa ∨ PosShiftLtPhaseDirectOk 320 m c := by
  revert lo
  induction fuel with
  | zero =>
      intro lo h hlom
      unfold ltPhaseCoverFastB at h
      simp only [decide_eq_true_eq] at h
      omega
  | succ fuel ih =>
      intro lo h hlom
      unfold ltPhaseCoverFastB at h
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
          let mx := ltPhaseTopMaxHi 320 (posPhaseNatLt lo c + lnPhaseExtraArg)
            lnErrQ (10 ^ 18) c lo hi
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨hlmx, hcell⟩, hrest⟩ := h
          by_cases hleft : m ≤ mx
          · exact Or.inr (ltPhaseCell_sound hcell hlom hleft)
          · exact ih (lo := mx + 1) hrest (by omega)

theorem lnWadToRayBody_positive_shift_ge_branch_cert {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hne : x ≠ 10 ^ 18)
    (hclt : evmClz x < 160) (hge : Sc ≤ mant x)
    (hcert : PosShiftGeBranchCert (mant x) (evmClz x)
      (int256 (lnWadToRayBody x))) :
    capLB (lnErrArg (int256 (lnWadToRayBody x))) lnErrQ x (10 ^ 18) := by
  rcases hcert with hres | hrest
  · exact lnWadToRayBody_positive_shift_ge_residue_or_direct h1 h2 hclt hge
      (Or.inl hres)
  rcases hrest with htop | hrest
  · exact lnWadToRayBody_positive_shift_ge_top_or_direct h1 h2 hne hclt hge
      (Or.inl htop)
  rcases hrest with hdirect | hrest
  · exact lnWadToRayBody_positive_shift_ge_top_or_direct h1 h2 hne hclt hge
      (Or.inr hdirect)
  rcases hrest with hphase | hgap
  · exact lnWadToRayBody_positive_shift_ge_phase_direct h1 h2 hne hclt hge hphase
  · have hx256 : x < 2 ^ 256 := by omega
    have htail :
        lnWadToRayBody x = lnTail (evmSub 160 (evmClz x)) (mant x) := by
      rw [lnWadToRayBody_eq_tail hx256]
      rfl
    obtain ⟨me, _hmlo, hmhi⟩ := mant_facts h1 h2
    have hmant_hi : mant x < MHI := by
      unfold mant
      rw [me]
      exact hmhi
    have hX := x1_nonneg_geF hge hmant_hi
    have hr0 := lnWadToRayBody_nonneg_of_clz_lt_160 h1 h2 hclt
    have hc160 : evmClz x ≤ 160 :=
      Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hclt (by decide : 160 ≤ 161))
    have hrm1 : -1 ≤ int256 (lnWadToRayBody x) :=
      Int.le_trans (by decide : (-1 : Int) ≤ 0) hr0
    have hsum := ge_phase_gap_direct_to_top
      (m := mant x) (c := evmClz x) (r := int256 (lnWadToRayBody x))
      hX hc160 hrm1 hgap.1 hgap.2
    have hsumTail :
        sumGE 320
          (lnErrArg (int256 (lnTail (evmSub 160 (evmClz x)) (mant x)))) lnErrQ
          (posTopX (evmClz x) (mant x)) (10 ^ 18) := by
      simpa [htail] using hsum
    exact pos_shift_direct_exact_of_sumGE h1 h2 hclt hsumTail

theorem lnWadToRayBody_positive_shift_lt_branch_cert {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hne : x ≠ 10 ^ 18)
    (hclt : evmClz x < 160) (hlt : mant x < Sc) (hband_lo : Sc - 45 ≤ mant x)
    (hcert : PosShiftLtBranchCert (mant x) (evmClz x)
      (int256 (lnWadToRayBody x))) :
    capLB (lnErrArg (int256 (lnWadToRayBody x))) lnErrQ x (10 ^ 18) := by
  rcases hcert with hres | hrest
  · exact lnWadToRayBody_positive_shift_lt_residue_or_direct h1 h2 hne hclt hlt hband_lo
      (Or.inl hres)
  rcases hrest with htop | hrest
  · exact lnWadToRayBody_positive_shift_lt_top_or_direct h1 h2 hne hclt hlt
      (Or.inl htop)
  rcases hrest with hdirect | hrest
  · exact lnWadToRayBody_positive_shift_lt_top_or_direct h1 h2 hne hclt hlt
      (Or.inr hdirect)
  rcases hrest with hphase | hgap
  · exact lnWadToRayBody_positive_shift_lt_phase_direct h1 h2 hne hclt hlt hphase
  · have hx256 : x < 2 ^ 256 := by omega
    have htail :
        lnWadToRayBody x = lnTail (evmSub 160 (evmClz x)) (mant x) := by
      rw [lnWadToRayBody_eq_tail hx256]
      rfl
    obtain ⟨hbr1, _hbr2⟩ := lnWadToRayBody_floor_bracket h1 h2 hne
    rw [show (4722366482869645213696 : Int) = 2 ^ 72 from by decide] at hbr1
    obtain ⟨me, hmlo, _hmhi⟩ := mant_facts h1 h2
    have hmant_lo : MLO ≤ mant x := by
      unfold mant
      rw [me]
      exact hmlo
    have hX := x1_nonpos_ltF hmant_lo hlt
    have hr0 := lnWadToRayBody_nonneg_of_clz_lt_160 h1 h2 hclt
    have hc160 : evmClz x ≤ 160 :=
      Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hclt (by decide : 160 ≤ 161))
    have hV0 : 0 ≤ int256 (x1W (zWord (mant x))) * 7450580596923828125 +
        ln2kInt (evmClz x) + lnBiasI := by
      have hR0 : 0 ≤ int256 (lnWadToRayBody x) * 2 ^ 72 :=
        Int.mul_nonneg hr0 (by decide)
      have h := Int.le_trans hR0 hbr1
      simpa [lnBiasI] using h
    have hneg := posNegXNat_le_posConstNat hX hc160 hV0
    have hrm1 : -1 ≤ int256 (lnWadToRayBody x) :=
      Int.le_trans (by decide : (-1 : Int) ≤ 0) hr0
    have hsum := lt_phase_gap_direct_to_top
      (m := mant x) (c := evmClz x) (r := int256 (lnWadToRayBody x))
      hX hc160 hneg hrm1 hgap.1 hgap.2
    have hsumTail :
        sumGE 320
          (lnErrArg (int256 (lnTail (evmSub 160 (evmClz x)) (mant x)))) lnErrQ
          (posTopX (evmClz x) (mant x)) (10 ^ 18) := by
      simpa [htail] using hsum
    exact pos_shift_direct_exact_of_sumGE h1 h2 hclt hsumTail

end LnFloorCert
