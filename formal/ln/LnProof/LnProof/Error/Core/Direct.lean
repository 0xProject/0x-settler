import LnProof.Floor.CutEquiv
import LnProof.Error.Cert
import LnProof.Error.Core.CutDefs
import LnProof.Error.Core.ExpMargin
import LnProof.Error.Core.ResidueCover
import LnProof.Error.Core.Budget

/-!
# Error bound — Direct

Direct-cover machinery: `expSum*`, `sumGEB`, and `PosShiftDirectCell` covers.
-/

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

namespace LnFloorCert

open LnYul LnFloor Common.Exp Common.Poly

attribute [local irreducible] lnWadToRayBody


def PosShiftTopDirectOk (n m c : Nat) : Prop :=
  sumGE n (lnErrArg (int256 (lnTail (evmSub 160 c) m))) lnErrQ
    (posTopX c m) (10 ^ 18)

def expSumState (p q : Nat) : Nat → Nat × Nat × Nat
  | 0 => (1, 1, 1)
  | n + 1 =>
      let s := expSumState p q n
      let pp := s.2.2 * p
      ((n + 1) * q * s.1 + pp, (n + 1) * q * s.2.1, pp)

theorem expSumState_spec (p q : Nat) :
    ∀ n, expSumState p q n = (expNum n p q, fact n * q ^ n, p ^ n)
  | 0 => by
      simp [expSumState, expNum, fact]
  | n + 1 => by
      simp [expSumState, expSumState_spec p q n, expNum, fact, Nat.pow_succ,
        Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

def expSumStateGo (p q : Nat) : Nat → Nat → Nat → Nat → Nat → Nat × Nat × Nat
  | 0, _i, e, d, pp => (e, d, pp)
  | k + 1, i, e, d, pp =>
      let pp' := pp * p
      expSumStateGo p q k (i + 1) ((i + 1) * q * e + pp') ((i + 1) * q * d) pp'

theorem expSumStateGo_spec (p q : Nat) :
    ∀ k i e d pp,
      expSumState p q i = (e, d, pp) →
        expSumStateGo p q k i e d pp = expSumState p q (i + k)
  | 0, i, e, d, pp, h => by
      simp [expSumStateGo, h]
  | k + 1, i, e, d, pp, h => by
      simp only [expSumStateGo]
      let pp' := pp * p
      have hnext : expSumState p q (i + 1) =
          ((i + 1) * q * e + pp', (i + 1) * q * d, pp') := by
        rw [show i + 1 = Nat.succ i by omega]
        simp [expSumState, h, pp']
      have ih := expSumStateGo_spec p q k (i + 1)
        ((i + 1) * q * e + pp') ((i + 1) * q * d) pp' hnext
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

def expSumStateFast (p q n : Nat) : Nat × Nat × Nat :=
  expSumStateGo p q n 0 1 1 1

theorem expSumStateFast_eq (p q n : Nat) :
    expSumStateFast p q n = expSumState p q n := by
  unfold expSumStateFast
  have h := expSumStateGo_spec p q n 0 1 1 1 (by simp [expSumState])
  simpa using h

def sumGEB (n p q y w : Nat) : Bool :=
  let s := expSumState p q n
  decide (y * s.2.1 ≤ s.1 * w)

theorem sumGE_of_sumGEB {n p q y w : Nat} (h : sumGEB n p q y w = true) :
    sumGE n p q y w := by
  unfold sumGEB at h
  simpa [sumGE, expSumState_spec p q n] using (of_decide_eq_true h)

structure PosShiftDirectCell where
  c : Nat
  lo : Nat
  hi : Nat
  n : Nat

def PosShiftDirectCell.Ok (cell : PosShiftDirectCell) : Prop :=
  MLO ≤ cell.lo ∧ cell.lo ≤ cell.hi ∧ cell.hi < MHI ∧ cell.c < 160 ∧
    sumGE cell.n (lnErrArg (int256 (lnTail (evmSub 160 cell.c) cell.lo))) lnErrQ
      (posTopX cell.c cell.hi) (10 ^ 18)

def PosShiftDirectCell.okB (cell : PosShiftDirectCell) : Bool :=
  decide (MLO ≤ cell.lo) &&
    decide (cell.lo ≤ cell.hi) &&
      decide (cell.hi < MHI) &&
        decide (cell.c < 160) &&
          decide (sumGE cell.n
            (lnErrArg (int256 (lnTail (evmSub 160 cell.c) cell.lo))) lnErrQ
            (posTopX cell.c cell.hi) (10 ^ 18))

def PosShiftDirectCell.Covers (cell : PosShiftDirectCell) (m c : Nat) : Prop :=
  c = cell.c ∧ cell.lo ≤ m ∧ m ≤ cell.hi

def PosShiftDirectCell.coversB (cell : PosShiftDirectCell) (m c : Nat) : Bool :=
  decide (c = cell.c) && decide (cell.lo ≤ m) && decide (m ≤ cell.hi)

theorem PosShiftDirectCell.ok_of_okB {cell : PosShiftDirectCell}
    (h : cell.okB = true) : cell.Ok := by
  unfold PosShiftDirectCell.okB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, hlohi⟩, hhi⟩, hc⟩, hsum⟩ := h
  exact ⟨hlo, hlohi, hhi, hc, hsum⟩

theorem PosShiftDirectCell.covers_of_coversB {cell : PosShiftDirectCell} {m c : Nat}
    (h : cell.coversB m c = true) : cell.Covers m c := by
  unfold PosShiftDirectCell.coversB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hc, hlo⟩, hhi⟩ := h
  exact ⟨hc, hlo, hhi⟩

def directCellsCoverB (cells : List PosShiftDirectCell) (m c : Nat) : Bool :=
  cells.any (fun cell => cell.okB && cell.coversB m c)

def directCellsCover320B (cells : List PosShiftDirectCell) (m c : Nat) : Bool :=
  cells.any (fun cell => decide (cell.n = 320) && cell.okB && cell.coversB m c)

def localDirectCell (m c : Nat) : PosShiftDirectCell :=
  { c := c, lo := max MLO (m - 16), hi := m, n := 320 }

def localDirectCertB (m c : Nat) : Bool :=
  (localDirectCell m c).okB

def residueOrDirectCertB (cells : List PosShiftDirectCell) (m c : Nat) (r : Int) : Bool :=
  residueGapOkB m c r || directCellsCover320B cells m c

def residueOrLocalDirectCertB (m c : Nat) (r : Int) : Bool :=
  residueGapOkB m c r || localDirectCertB m c

def posShiftDirectCells : List PosShiftDirectCell := []

theorem posTopX_mono_m {c m hi : Nat} (hm : m ≤ hi) :
    posTopX c m ≤ posTopX c hi := by
  unfold posTopX
  have hmul : (m + 1) * 2 ^ (160 - c) ≤ (hi + 1) * 2 ^ (160 - c) :=
    Nat.mul_le_mul_right _ (by omega)
  have hpos : 0 < (m + 1) * 2 ^ (160 - c) :=
    Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (by decide))
  omega

theorem lnTail_mono_m {c lo m hi : Nat}
    (hlo : MLO ≤ lo) (hlom : lo ≤ m) (hmhi : m ≤ hi) (hhi : hi < MHI)
    (hc : c < 256) :
    int256 (lnTail (evmSub 160 c) lo) ≤ int256 (lnTail (evmSub 160 c) m) := by
  have hmhi' : m < MHI := by omega
  have hw := ln2k_bound (c := c) hc
  exact tail_mono hlo hlom hmhi' hw.1 hw.2

theorem PosShiftDirectCell.sound {cell : PosShiftDirectCell} {m c : Nat}
    (hok : cell.Ok) (hcov : cell.Covers m c) :
    PosShiftTopDirectOk cell.n m c := by
  obtain ⟨hlo, hlohi, hhi, _hc, hsum⟩ := hok
  obtain ⟨hc_eq, hmlo, hmhi⟩ := hcov
  subst c
  unfold PosShiftTopDirectOk
  refine sumGE_exact_mono (n := cell.n)
    (p0 := lnErrArg (int256 (lnTail (evmSub 160 cell.c) cell.lo)))
    (p := lnErrArg (int256 (lnTail (evmSub 160 cell.c) m)))
    (y0 := posTopX cell.c cell.hi) (y := posTopX cell.c m) ?_ ?_ hsum
  · exact lnErrArg_mono (lnTail_mono_m hlo hmlo hmhi hhi (by omega))
  · exact posTopX_mono_m hmhi

theorem direct_of_cells_cover {cells : List PosShiftDirectCell} {m c : Nat}
    (h : directCellsCoverB cells m c = true) :
    ∃ n, PosShiftTopDirectOk n m c := by
  unfold directCellsCoverB at h
  rw [List.any_eq_true] at h
  obtain ⟨cell, _hmem, hokcov⟩ := h
  simp only [Bool.and_eq_true] at hokcov
  obtain ⟨hok, hcov⟩ := hokcov
  exact ⟨cell.n, PosShiftDirectCell.sound
    (PosShiftDirectCell.ok_of_okB hok)
    (PosShiftDirectCell.covers_of_coversB hcov)⟩

theorem direct320_of_cells_cover {cells : List PosShiftDirectCell} {m c : Nat}
    (h : directCellsCover320B cells m c = true) :
    PosShiftTopDirectOk 320 m c := by
  unfold directCellsCover320B at h
  rw [List.any_eq_true] at h
  obtain ⟨cell, _hmem, hcert⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcert
  obtain ⟨⟨hn, hok⟩, hcov⟩ := hcert
  have hs := PosShiftDirectCell.sound
    (PosShiftDirectCell.ok_of_okB hok)
    (PosShiftDirectCell.covers_of_coversB hcov)
  simpa [hn] using hs

theorem residue_or_direct_of_certB {cells : List PosShiftDirectCell} {m c : Nat} {r : Int}
    (hc : c ≤ 160) (h : residueOrDirectCertB cells m c r = true) :
    PosShiftResidueOk m c r ∨ PosShiftTopDirectOk 320 m c := by
  unfold residueOrDirectCertB at h
  simp only [Bool.or_eq_true] at h
  rcases h with hres | hdir
  · exact Or.inl (PosShiftResidueOk_of_gapB hc hres)
  · exact Or.inr (direct320_of_cells_cover hdir)

theorem residue_or_direct_of_local_certB {m c : Nat} {r : Int}
    (hc : c ≤ 160) (h : residueOrLocalDirectCertB m c r = true) :
    PosShiftResidueOk m c r ∨ PosShiftTopDirectOk 320 m c := by
  unfold residueOrLocalDirectCertB localDirectCertB at h
  simp only [Bool.or_eq_true] at h
  rcases h with hres | hdir
  · exact Or.inl (PosShiftResidueOk_of_gapB hc hres)
  · have hokCell := PosShiftDirectCell.ok_of_okB hdir
    have hlohi := hokCell.2.1
    have hcell : (localDirectCell m c).Covers m c := by
      simpa [localDirectCell, PosShiftDirectCell.Covers] using
        (⟨rfl, hlohi, Nat.le_refl m⟩ :
          c = c ∧ (localDirectCell m c).lo ≤ m ∧ m ≤ (localDirectCell m c).hi)
    have hs := PosShiftDirectCell.sound hokCell hcell
    have hs320 : PosShiftTopDirectOk 320 m c := by
      simpa [localDirectCell] using hs
    exact Or.inr hs320

theorem posPhaseNatGe_mono_m {lo m c : Nat}
    (hlo : Sc ≤ lo) (hlom : lo ≤ m) (hmhi : m < MHI) :
    posPhaseNatGe lo c ≤ posPhaseNatGe m c := by
  unfold posPhaseNatGe
  have hmlo : MLO ≤ lo := by
    simp only [Sc, MLO] at hlo ⊢
    omega
  have hx := LnYul.r1_mono hmlo hlom hmhi
  have hxNat : (int256 (x1W (zWord lo))).toNat ≤
      (int256 (x1W (zWord m))).toNat :=
    Int.toNat_le_toNat hx
  have hmul : (int256 (x1W (zWord lo))).toNat * lnPhaseScaleN * lnErrorBoundDen ≤
      (int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen := by
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hxNat)
  omega

theorem posNegXNat_antitone_m {lo m : Nat}
    (hlo : MLO ≤ lo) (hlom : lo ≤ m) (hmhi : m < MHI) :
    posNegXNat m ≤ posNegXNat lo := by
  unfold posNegXNat
  have hx := LnYul.r1_mono hlo hlom hmhi
  have hneg : -int256 (x1W (zWord m)) ≤ -int256 (x1W (zWord lo)) := by
    omega
  have hn : (-int256 (x1W (zWord m))).toNat ≤
      (-int256 (x1W (zWord lo))).toNat :=
    Int.toNat_le_toNat hneg
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hn)

theorem posPhaseNatLt_mono_m {lo m c : Nat}
    (hlo : MLO ≤ lo) (hlom : lo ≤ m) (hmhi : m < MHI) :
    posPhaseNatLt lo c ≤ posPhaseNatLt m c := by
  unfold posPhaseNatLt
  have hn := posNegXNat_antitone_m (lo := lo) (m := m) hlo hlom hmhi
  exact Nat.sub_le_sub_left hn (posConstNat c)

end LnFloorCert
