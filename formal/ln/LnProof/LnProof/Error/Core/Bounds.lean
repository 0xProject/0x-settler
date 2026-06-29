import LnProof.Floor.CutEquiv
import LnProof.Error.Cert
import LnProof.Error.Core.CutDefs
import LnProof.Error.Core.Args
import LnProof.Error.Core.Residue
import LnProof.Error.Core.ResidueCover
import LnProof.Error.Core.Budget
import LnProof.Error.Core.Direct
import LnProof.Error.Core.PhaseCover

/-!
# Error bound — Bounds

`minPosAvail` casts, the `posPhaseNat*_le_lnErrArg` family, top-budget cells, and the `lo_*_budget_exact` bridges.
-/

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

namespace LnFloorCert

open LnYul LnFloor Common.Exp Common.Poly

attribute [local irreducible] lnWadToRayBody


theorem minPosAvail_cast :
    ((minPosAvail : Nat) : Int) =
      (lnErrorExtraNum : Int) * twoPow99I +
        twoPow27I * (lnErrorBoundDen : Int) := by
  unfold minPosAvail lnPhaseExtraArg twoPow99N twoPow27N twoPow99I twoPow27I
  unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen
  decide +kernel

theorem posPhaseNatGe_minAvail_le_lnErrArg {m c : Nat}
    (hge : Sc ≤ m) (hmhi : m < MHI) (hc : c < 160) :
    posPhaseNatGe m c + minPosAvail ≤
      lnErrArg (int256 (lnTail (evmSub 160 c) m)) := by
  let r := int256 (lnTail (evmSub 160 c) m)
  have hmlo : MLO ≤ m := by
    simp only [Sc, MLO] at hge ⊢
    omega
  have hX := x1_nonneg_geF hge hmhi
  have hgap : 1 ≤ posResidueGap m c r := by
    simpa [r] using (posResidueGap_bounds hmlo hmhi hc).1
  have hdecomp := lnErrArg_eq_posPhase_gap (m := m) (c := c) hmlo hmhi hc
  change ((lnErrArg r : Nat) : Int) =
      posPhaseI m c * (lnErrorBoundDen : Int) +
        (lnErrorExtraNum : Int) * twoPow99I +
          posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) at hdecomp
  apply Int.ofNat_le.mp
  rw [Int.natCast_add, posPhaseNatGe_cast hX, minPosAvail_cast, hdecomp]
  have h27 : 0 ≤ twoPow27I := by
    unfold twoPow27I
    decide
  have hden : 0 ≤ (lnErrorBoundDen : Int) := by
    change (0 : Int) ≤ 1000000000
    decide
  have hgap27 :
      1 * twoPow27I ≤ posResidueGap m c r * twoPow27I :=
    Int.mul_le_mul_of_nonneg_right hgap h27
  have hgapDen :
      1 * twoPow27I * (lnErrorBoundDen : Int) ≤
        posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) :=
    Int.mul_le_mul_of_nonneg_right hgap27 hden
  have hgapDen' :
      twoPow27I * (lnErrorBoundDen : Int) ≤
        posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) := by
    simpa [Int.one_mul] using hgapDen
  have hinner :
      (lnErrorExtraNum : Int) * twoPow99I +
          twoPow27I * (lnErrorBoundDen : Int) ≤
        (lnErrorExtraNum : Int) * twoPow99I +
          posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) :=
    Int.add_le_add_left hgapDen' _
  have hmain :
      posPhaseI m c * (lnErrorBoundDen : Int) +
          ((lnErrorExtraNum : Int) * twoPow99I +
            twoPow27I * (lnErrorBoundDen : Int)) ≤
        posPhaseI m c * (lnErrorBoundDen : Int) +
          ((lnErrorExtraNum : Int) * twoPow99I +
            posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int)) :=
    Int.add_le_add_left hinner _
  simpa [Int.add_assoc] using hmain

theorem posPhaseNatLt_minAvail_le_lnErrArg {m c : Nat}
    (hmlo : MLO ≤ m) (hmlt : m < Sc) (hc : c < 160) :
    posPhaseNatLt m c + minPosAvail ≤
      lnErrArg (int256 (lnTail (evmSub 160 c) m)) := by
  let r := int256 (lnTail (evmSub 160 c) m)
  have hmhi : m < MHI := by
    simp only [Sc, MHI] at hmlt ⊢
    omega
  have hX := x1_nonpos_ltF hmlo hmlt
  have hV0 : 0 ≤
      int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c + lnBiasI := by
    simpa [posAccI] using posAccI_nonneg hmlo hmhi hc
  have hneg := posNegXNat_le_posConstNat hX (by omega : c ≤ 160) hV0
  have hgap : 1 ≤ posResidueGap m c r := by
    simpa [r] using (posResidueGap_bounds hmlo hmhi hc).1
  have hdecomp := lnErrArg_eq_posPhase_gap (m := m) (c := c) hmlo hmhi hc
  change ((lnErrArg r : Nat) : Int) =
      posPhaseI m c * (lnErrorBoundDen : Int) +
        (lnErrorExtraNum : Int) * twoPow99I +
          posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) at hdecomp
  apply Int.ofNat_le.mp
  rw [Int.natCast_add, posPhaseNatLt_cast hX hneg, minPosAvail_cast, hdecomp]
  have h27 : 0 ≤ twoPow27I := by
    unfold twoPow27I
    decide
  have hden : 0 ≤ (lnErrorBoundDen : Int) := by
    change (0 : Int) ≤ 1000000000
    decide
  have hgap27 :
      1 * twoPow27I ≤ posResidueGap m c r * twoPow27I :=
    Int.mul_le_mul_of_nonneg_right hgap h27
  have hgapDen :
      1 * twoPow27I * (lnErrorBoundDen : Int) ≤
        posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) :=
    Int.mul_le_mul_of_nonneg_right hgap27 hden
  have hgapDen' :
      twoPow27I * (lnErrorBoundDen : Int) ≤
        posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) := by
    simpa [Int.one_mul] using hgapDen
  have hinner :
      (lnErrorExtraNum : Int) * twoPow99I +
          twoPow27I * (lnErrorBoundDen : Int) ≤
        (lnErrorExtraNum : Int) * twoPow99I +
          posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int) :=
    Int.add_le_add_left hgapDen' _
  have hmain :
      posPhaseI m c * (lnErrorBoundDen : Int) +
          ((lnErrorExtraNum : Int) * twoPow99I +
            twoPow27I * (lnErrorBoundDen : Int)) ≤
        posPhaseI m c * (lnErrorBoundDen : Int) +
          ((lnErrorExtraNum : Int) * twoPow99I +
            posResidueGap m c r * twoPow27I * (lnErrorBoundDen : Int)) :=
    Int.add_le_add_left hinner _
  simpa [Int.add_assoc] using hmain

theorem posAvailGe_min {m c : Nat}
    (hge : Sc ≤ m) (hmhi : m < MHI) (hc : c < 160) :
    minPosAvail ≤
      posAvailGe m c (int256 (lnTail (evmSub 160 c) m)) := by
  unfold posAvailGe
  have h := posPhaseNatGe_minAvail_le_lnErrArg hge hmhi hc
  omega

theorem posAvailLt_min {m c : Nat}
    (hmlo : MLO ≤ m) (hmlt : m < Sc) (hc : c < 160) :
    minPosAvail ≤
      posAvailLt m c (int256 (lnTail (evmSub 160 c) m)) := by
  unfold posAvailLt
  have h := posPhaseNatLt_minAvail_le_lnErrArg hmlo hmlt hc
  omega

theorem wadRayNum_mono {x y : Nat} (hxy : x ≤ y) : wadRayNum x ≤ wadRayNum y := by
  unfold wadRayNum
  exact Nat.mul_le_mul_right _ hxy

theorem posBaseYGe_mono_m {lo m c : Nat} (hlom : lo ≤ m) :
    posBaseYGe lo c ≤ posBaseYGe m c := by
  unfold posBaseYGe
  have h1 :
      lo * 9999999999999999999999999996615 ≤
        m * 9999999999999999999999999996615 :=
    Nat.mul_le_mul_right _ hlom
  have h2 :
      (lo * 9999999999999999999999999996615) *
          (2 * (10 ^ 40 - 1)) ^ (160 - c) ≤
        (m * 9999999999999999999999999996615) *
          (2 * (10 ^ 40 - 1)) ^ (160 - c) :=
    Nat.mul_le_mul_right _ h1
  exact Nat.mul_le_mul_right _ h2

theorem posBaseYLt_mono_m {lo m c : Nat} (hlom : lo ≤ m) :
    posBaseYLt lo c ≤ posBaseYLt m c := by
  unfold posBaseYLt
  have h1 :
      lo * 9999999999999999999999999996615 ≤
        m * 9999999999999999999999999996615 :=
    Nat.mul_le_mul_right _ hlom
  exact Nat.mul_le_mul_left _ h1

theorem geTopBudgetCoarseCellOkB_sound {lo hi m c : Nat}
    (h : geTopBudgetCoarseCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGeTopBudgetIneqOk m c := by
  unfold geTopBudgetCoarseCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, _hlohi⟩, hhi⟩, hc⟩, hineq⟩ := h
  unfold PosShiftGeTopBudgetIneqOk PosShiftGeBudgetIneqOk
  let r := int256 (lnTail (evmSub 160 c) m)
  have hleft :
      wadRayNum (posTopX c m) * (posBaseWGe c * lnErrQ) ≤
        wadRayNum (posTopX c hi) * (posBaseWGe c * lnErrQ) := by
    exact Nat.mul_le_mul_right _ (wadRayNum_mono (posTopX_mono_m hmhi))
  have hbase : posBaseYGe lo c ≤ posBaseYGe m c :=
    posBaseYGe_mono_m hlom
  have havail : minPosAvail ≤ posAvailGe m c r :=
    posAvailGe_min (m := m) (c := c) (by omega) (by omega) hc
  have hmargin : lnErrQ + minPosAvail ≤ lnErrQ + posAvailGe m c r :=
    Nat.add_le_add_left havail lnErrQ
  have hright :
      (posBaseYGe lo c * (lnErrQ + minPosAvail)) * wadRayStrictDen ≤
        (posBaseYGe m c * (lnErrQ + posAvailGe m c r)) * wadRayStrictDen := by
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hbase hmargin)
  exact Nat.le_trans hleft (Nat.le_trans hineq hright)

theorem ltTopBudgetCoarseCellOkB_sound {lo hi m c : Nat}
    (h : ltTopBudgetCoarseCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftLtTopBudgetIneqOk m c := by
  unfold ltTopBudgetCoarseCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, _hlohi⟩, hhi⟩, hc⟩, hineq⟩ := h
  unfold PosShiftLtTopBudgetIneqOk PosShiftLtBudgetIneqOk
  let r := int256 (lnTail (evmSub 160 c) m)
  have hleft :
      wadRayNum (posTopX c m) * (posBaseWLt c * lnErrQ) ≤
        wadRayNum (posTopX c hi) * (posBaseWLt c * lnErrQ) := by
    exact Nat.mul_le_mul_right _ (wadRayNum_mono (posTopX_mono_m hmhi))
  have hbase : posBaseYLt lo c ≤ posBaseYLt m c :=
    posBaseYLt_mono_m hlom
  have havail : minPosAvail ≤ posAvailLt m c r :=
    posAvailLt_min (m := m) (c := c) (by omega) (by omega) hc
  have hmargin : lnErrQ + minPosAvail ≤ lnErrQ + posAvailLt m c r :=
    Nat.add_le_add_left havail lnErrQ
  have hright :
      (posBaseYLt lo c * (lnErrQ + minPosAvail)) * wadRayStrictDen ≤
        (posBaseYLt m c * (lnErrQ + posAvailLt m c r)) * wadRayStrictDen := by
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hbase hmargin)
  exact Nat.le_trans hleft (Nat.le_trans hineq hright)

theorem geTopBudgetRunCellOkB_sound {lo hi m c : Nat}
    (h : geTopBudgetRunCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftGeTopBudgetIneqOk m c := by
  unfold geTopBudgetRunCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hloSc, hlohi⟩, hhi⟩, hc⟩, hrun⟩ := h
  obtain ⟨hboundary, hineq⟩ := hrun
  have hlo : MLO ≤ lo := by
    simp only [Sc, MLO] at hloSc ⊢
    omega
  let rlo := int256 (lnTail (evmSub 160 c) lo)
  let rm := int256 (lnTail (evmSub 160 c) m)
  let rhi := int256 (lnTail (evmSub 160 c) hi)
  have hmhi' : m < MHI := by omega
  have htailM : rm = rlo := by
    simpa [rm, rlo] using
      lnTail_eq_of_residue_run hlo hlom hmhi hhi hc hboundary
  have htailHi : rhi = rlo := by
    simpa [rhi, rlo] using
      lnTail_eq_of_residue_run hlo hlohi (Nat.le_refl hi) hhi hc hboundary
  unfold PosShiftGeTopBudgetIneqOk PosShiftGeBudgetIneqOk
  have hleft :
      wadRayNum (posTopX c m) * (posBaseWGe c * lnErrQ) ≤
        wadRayNum (posTopX c hi) * (posBaseWGe c * lnErrQ) := by
    exact Nat.mul_le_mul_right _ (wadRayNum_mono (posTopX_mono_m hmhi))
  have hbase : posBaseYGe lo c ≤ posBaseYGe m c :=
    posBaseYGe_mono_m hlom
  have hphase_m_hi : posPhaseNatGe m c ≤ posPhaseNatGe hi c :=
    posPhaseNatGe_mono_m (lo := m) (m := hi) (c := c) (by omega) hmhi hhi
  have havail : posAvailGe hi c rlo ≤ posAvailGe m c rm := by
    unfold posAvailGe
    rw [htailM]
    exact Nat.sub_le_sub_left hphase_m_hi (lnErrArg rlo)
  have hmargin : lnErrQ + posAvailGe hi c rlo ≤ lnErrQ + posAvailGe m c rm :=
    Nat.add_le_add_left havail lnErrQ
  have hright :
      (posBaseYGe lo c * (lnErrQ + posAvailGe hi c rlo)) * wadRayStrictDen ≤
        (posBaseYGe m c * (lnErrQ + posAvailGe m c rm)) * wadRayStrictDen := by
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hbase hmargin)
  have hineq' :
      wadRayNum (posTopX c hi) * (posBaseWGe c * lnErrQ) ≤
        (posBaseYGe lo c * (lnErrQ + posAvailGe hi c rlo)) * wadRayStrictDen := by
    simpa [rlo] using hineq
  have hle := Nat.le_trans hleft (Nat.le_trans hineq' hright)
  simpa [rm] using hle

theorem ltTopBudgetRunCellOkB_sound {lo hi m c : Nat}
    (h : ltTopBudgetRunCellOkB lo hi c = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) :
    PosShiftLtTopBudgetIneqOk m c := by
  unfold ltTopBudgetRunCellOkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlo, hlohi⟩, hhiSc⟩, hc⟩, hrun⟩ := h
  obtain ⟨hboundary, hineq⟩ := hrun
  have hhi : hi < MHI := by
    simp only [Sc, MHI] at hhiSc ⊢
    omega
  let rlo := int256 (lnTail (evmSub 160 c) lo)
  let rm := int256 (lnTail (evmSub 160 c) m)
  let rhi := int256 (lnTail (evmSub 160 c) hi)
  have hmhi' : m < MHI := by omega
  have htailM : rm = rlo := by
    simpa [rm, rlo] using
      lnTail_eq_of_residue_run hlo hlom hmhi hhi hc hboundary
  have htailHi : rhi = rlo := by
    simpa [rhi, rlo] using
      lnTail_eq_of_residue_run hlo hlohi (Nat.le_refl hi) hhi hc hboundary
  unfold PosShiftLtTopBudgetIneqOk PosShiftLtBudgetIneqOk
  have hleft :
      wadRayNum (posTopX c m) * (posBaseWLt c * lnErrQ) ≤
        wadRayNum (posTopX c hi) * (posBaseWLt c * lnErrQ) := by
    exact Nat.mul_le_mul_right _ (wadRayNum_mono (posTopX_mono_m hmhi))
  have hbase : posBaseYLt lo c ≤ posBaseYLt m c :=
    posBaseYLt_mono_m hlom
  have hphase_m_hi : posPhaseNatLt m c ≤ posPhaseNatLt hi c :=
    posPhaseNatLt_mono_m (lo := m) (m := hi) (c := c) (by omega) hmhi (by
      simp only [Sc, MHI] at hhiSc ⊢
      omega)
  have havail : posAvailLt hi c rlo ≤ posAvailLt m c rm := by
    unfold posAvailLt
    rw [htailM]
    exact Nat.sub_le_sub_left hphase_m_hi (lnErrArg rlo)
  have hmargin : lnErrQ + posAvailLt hi c rlo ≤ lnErrQ + posAvailLt m c rm :=
    Nat.add_le_add_left havail lnErrQ
  have hright :
      (posBaseYLt lo c * (lnErrQ + posAvailLt hi c rlo)) * wadRayStrictDen ≤
        (posBaseYLt m c * (lnErrQ + posAvailLt m c rm)) * wadRayStrictDen := by
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hbase hmargin)
  have hineq' :
      wadRayNum (posTopX c hi) * (posBaseWLt c * lnErrQ) ≤
        (posBaseYLt lo c * (lnErrQ + posAvailLt hi c rlo)) * wadRayStrictDen := by
    simpa [rlo] using hineq
  have hle := Nat.le_trans hleft (Nat.le_trans hineq' hright)
  simpa [rm] using hle

theorem posPhaseNatLt_le_lnErrArg {m c : Nat} {r : Int}
    (hX : int256 (x1W (zWord m)) ≤ 0) (hc : c ≤ 160)
    (hneg : posNegXNat m ≤ posConstNat c)
    (hr : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI < (r + 1) * 2 ^ 72)
    (hr0 : -1 ≤ r) :
    posPhaseNatLt m c ≤ lnErrArg r := by
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
  rw [posPhaseNatLt_cast hX hneg]
  unfold lnErrArg
  rw [Int.natCast_mul, Int.toNat_of_nonneg harg]
  have hnon : 0 ≤ 698600000 * twoPow99I := by
    unfold twoPow99I
    decide
  have hle := Int.le_trans (Int.le_add_of_nonneg_right hnon) hcore
  simpa [lnErrorBoundDen, lnErrorBoundNum, twoPow99I] using hle

theorem posPhaseNatGe_extra_le_lnErrArg {m c : Nat} {r : Int}
    (hge : Sc ≤ m) (hmhi : m < MHI) (hc : c ≤ 160)
    (hr : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI < (r + 1) * 2 ^ 72)
    (hr0 : -1 ≤ r) :
    posPhaseNatGe m c + lnPhaseExtraArg ≤ lnErrArg r := by
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
  rw [Int.natCast_add, posPhaseNatGe_cast hX]
  unfold lnPhaseExtraArg lnErrArg
  have htarget : ((((r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)).toNat *
      2 ^ 99 : Nat) : Int)) =
      (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) * twoPow99I := by
    rw [Int.natCast_mul, Int.toNat_of_nonneg harg]
    unfold twoPow99I
    rfl
  have hextra : (((lnErrorExtraNum * twoPow99N : Nat) : Int)) =
      (lnErrorExtraNum : Int) * twoPow99I := by
    unfold twoPow99N twoPow99I
    rfl
  rw [htarget, hextra]
  simpa [lnErrorBoundDen, lnErrorBoundNum, lnErrorExtraNum, twoPow99N, twoPow99I]
    using hcore

theorem posPhaseNatLt_extra_le_lnErrArg {m c : Nat} {r : Int}
    (hX : int256 (x1W (zWord m)) ≤ 0) (hc : c ≤ 160)
    (hneg : posNegXNat m ≤ posConstNat c)
    (hr : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI < (r + 1) * 2 ^ 72)
    (hr0 : -1 ≤ r) :
    posPhaseNatLt m c + lnPhaseExtraArg ≤ lnErrArg r := by
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
  rw [Int.natCast_add, posPhaseNatLt_cast hX hneg]
  unfold lnPhaseExtraArg lnErrArg
  have htarget : ((((r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)).toNat *
      2 ^ 99 : Nat) : Int)) =
      (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) * twoPow99I := by
    rw [Int.natCast_mul, Int.toNat_of_nonneg harg]
    unfold twoPow99I
    rfl
  have hextra : (((lnErrorExtraNum * twoPow99N : Nat) : Int)) =
      (lnErrorExtraNum : Int) * twoPow99I := by
    unfold twoPow99N twoPow99I
    rfl
  rw [htarget, hextra]
  simpa [lnErrorBoundDen, lnErrorBoundNum, lnErrorExtraNum, twoPow99N, twoPow99I]
    using hcore

theorem posPhaseNatGe_gap_extra_le_lnErrArg {m c : Nat} {r : Int}
    (hX : 0 ≤ int256 (x1W (zWord m))) (hc : c ≤ 160) (hr0 : -1 ≤ r)
    (hgap : PosShiftDirectResidueGapOk m c r) :
    posPhaseNatGe m c + lnPhaseExtraArg + lnDirectGapArg ≤ lnErrArg r := by
  have hres := direct_residue_phase_bound (m := m) (c := c) (r := r) hc hgap
  have hcore := pos_direct_residue_arg_le_int hres
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
  rw [Int.natCast_add, Int.natCast_add, posPhaseNatGe_cast hX]
  unfold lnPhaseExtraArg lnDirectGapArg lnErrArg
  have htarget : ((((r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)).toNat *
      2 ^ 99 : Nat) : Int)) =
      (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) * twoPow99I := by
    rw [Int.natCast_mul, Int.toNat_of_nonneg harg]
    unfold twoPow99I
    rfl
  have hextra : (((lnErrorExtraNum * twoPow99N : Nat) : Int)) =
      (lnErrorExtraNum : Int) * twoPow99I := by
    unfold twoPow99N twoPow99I
    rfl
  have hgapcast :
      (((lnErrorDirectResidueGap * twoPow27N * lnErrorBoundDen : Nat) : Int)) =
        (lnErrorDirectResidueGap : Int) * twoPow27I * (lnErrorBoundDen : Int) := by
    unfold lnErrorDirectResidueGap twoPow27N twoPow27I lnErrorBoundDen
    decide
  rw [htarget, hextra, hgapcast]
  simpa [lnErrorBoundDen, lnErrorBoundNum, lnErrorExtraNum, twoPow99I]
    using hcore

theorem posPhaseNatLt_gap_extra_le_lnErrArg {m c : Nat} {r : Int}
    (hX : int256 (x1W (zWord m)) ≤ 0) (hc : c ≤ 160)
    (hneg : posNegXNat m ≤ posConstNat c) (hr0 : -1 ≤ r)
    (hgap : PosShiftDirectResidueGapOk m c r) :
    posPhaseNatLt m c + lnPhaseExtraArg + lnDirectGapArg ≤ lnErrArg r := by
  have hres := direct_residue_phase_bound (m := m) (c := c) (r := r) hc hgap
  have hcore := pos_direct_residue_arg_le_int hres
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
  rw [Int.natCast_add, Int.natCast_add, posPhaseNatLt_cast hX hneg]
  unfold lnPhaseExtraArg lnDirectGapArg lnErrArg
  have htarget : ((((r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)).toNat *
      2 ^ 99 : Nat) : Int)) =
      (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) * twoPow99I := by
    rw [Int.natCast_mul, Int.toNat_of_nonneg harg]
    unfold twoPow99I
    rfl
  have hextra : (((lnErrorExtraNum * twoPow99N : Nat) : Int)) =
      (lnErrorExtraNum : Int) * twoPow99I := by
    unfold twoPow99N twoPow99I
    rfl
  have hgapcast :
      (((lnErrorDirectResidueGap * twoPow27N * lnErrorBoundDen : Nat) : Int)) =
        (lnErrorDirectResidueGap : Int) * twoPow27I * (lnErrorBoundDen : Int) := by
    unfold lnErrorDirectResidueGap twoPow27N twoPow27I lnErrorBoundDen
    decide
  rw [htarget, hextra, hgapcast]
  simpa [lnErrorBoundDen, lnErrorBoundNum, lnErrorExtraNum, twoPow99I]
    using hcore

theorem ge_phase_gap_direct_to_top {n m c : Nat} {r : Int}
    (hX : 0 ≤ int256 (x1W (zWord m))) (hc : c ≤ 160) (hr0 : -1 ≤ r)
    (hgap : PosShiftDirectResidueGapOk m c r)
    (hdirect : PosShiftGePhaseGapDirectOk n m c) :
    sumGE n (lnErrArg r) lnErrQ (posTopX c m) (10 ^ 18) := by
  unfold PosShiftGePhaseGapDirectOk at hdirect
  exact sumGE_exact_mono
    (posPhaseNatGe_gap_extra_le_lnErrArg hX hc hr0 hgap)
    (Nat.le_refl _) hdirect

theorem lt_phase_gap_direct_to_top {n m c : Nat} {r : Int}
    (hX : int256 (x1W (zWord m)) ≤ 0) (hc : c ≤ 160)
    (hneg : posNegXNat m ≤ posConstNat c) (hr0 : -1 ≤ r)
    (hgap : PosShiftDirectResidueGapOk m c r)
    (hdirect : PosShiftLtPhaseGapDirectOk n m c) :
    sumGE n (lnErrArg r) lnErrQ (posTopX c m) (10 ^ 18) := by
  unfold PosShiftLtPhaseGapDirectOk at hdirect
  exact sumGE_exact_mono
    (posPhaseNatLt_gap_extra_le_lnErrArg hX hc hneg hr0 hgap)
    (Nat.le_refl _) hdirect

theorem capLB_first_order_self (p q : Nat) :
    capLB p q (q + p) q := by
  refine ⟨1, ?_⟩
  simp only [fact, expNum, Nat.pow_one, Nat.mul_one, Nat.one_mul, Nat.zero_add]
  exact Nat.le_refl _

theorem capLB_cancel_first_order_budget {arg const neg q C W G V yT wT : Nat}
    (hq : 0 < q)
    (hconst : capLB const q C W)
    (hneg : capUB neg q G V)
    (hneg_le : neg ≤ const)
    (hphase : const - neg ≤ arg)
    (hW : 0 < W)
    (hG : 0 < G)
    (hbudget : yT * ((W * q) * G) ≤
      ((C * (q + (arg - (const - neg)))) * V) * wT) :
    capLB arg q yT wT := by
  have capE := capLB_first_order_self (arg - (const - neg)) q
  have hsum0 := capLB_mul hconst capE
  have hsplit : const + (arg - (const - neg)) =
      ((const - neg) + (arg - (const - neg))) + neg := by
    calc
      const + (arg - (const - neg)) =
          (const - neg + neg) + (arg - (const - neg)) := by
            rw [Nat.sub_add_cancel hneg_le]
      _ = ((const - neg) + (arg - (const - neg))) + neg := by
            omega
  rw [hsplit] at hsum0
  have capV := capLB_cancel (q := q) hq hsum0 hneg
  have harg : (const - neg) + (arg - (const - neg)) = arg := by
    exact Nat.add_sub_of_le hphase
  rw [harg] at capV
  refine capLB_weaken ?_ capV hbudget
  exact Nat.mul_pos (Nat.mul_pos hW hq) hG

theorem pos_residue_arg_le_int {A r : Int}
    (hres : A * (lnErrorBoundDen : Int) + (lnErrorCoarsePosResidue : Int) ≤
      (r + 1) * twoPow99I * (lnErrorBoundDen : Int)) :
    A * (lnErrorBoundDen : Int) + (lnErrorExtraNum : Int) * twoPow99I +
        (lnErrorCoarsePosResidue : Int) ≤
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
  unfold twoPow99I at hres ⊢
  omega

theorem pos_ge_residue_arg_le_int {A r : Int}
    (hres : A * (lnErrorBoundDen : Int) + (lnErrorCoarseGePosResidue : Int) ≤
      (r + 1) * twoPow99I * (lnErrorBoundDen : Int)) :
    A * (lnErrorBoundDen : Int) + (lnErrorExtraNum : Int) * twoPow99I +
        (lnErrorCoarseGePosResidue : Int) ≤
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
  unfold twoPow99I at hres ⊢
  omega

theorem errBudgetL_fold {m k : Nat} (hm : Sc - 45 ≤ m) (hk : k ≤ 159) :
    (m + 1) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142) ≤
      m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k * (10 ^ 31 - 3384) *
        (10 ^ 31 + lnErrorCoarsePosBudgetCap) * (10 ^ 31 - 10) * 10 ^ 18) := by
  have hb := errBudgetL_le (k := k) hk
  have hcross : (m + 1) * (Sc - 45) ≤ m * ((Sc - 45) + 1) := by
    have e1 : (m + 1) * (Sc - 45) = m * (Sc - 45) + (Sc - 45) := by
      rw [Nat.add_mul, Nat.one_mul]
    have e2 : m * ((Sc - 45) + 1) = m * (Sc - 45) + m := by
      rw [Nat.mul_add, Nat.mul_one]
    omega
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < Sc - 45 by decide)
  calc (Sc - 45) * ((m + 1) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142))
      = ((m + 1) * (Sc - 45)) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142) := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm]
    _ ≤ (m * ((Sc - 45) + 1)) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142) :=
        Nat.mul_le_mul_right _ hcross
    _ = m * (((Sc - 45) + 1) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142)) := by
        simp only [Nat.mul_assoc]
    _ = m * (((Sc - 45) + 1) * 2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142) := by
        simp only [Nat.mul_assoc]
    _ ≤ m * ((Sc - 45) * (10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarsePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18) :=
        Nat.mul_le_mul_left _ hb
    _ = (Sc - 45) * (m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarsePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18)) := by
        simp only [Nat.mul_comm, Nat.mul_left_comm]

theorem errBudgetL_ge_fold {m k : Nat} (hm : Sc ≤ m) (hk : k ≤ 159) :
    (m + 1) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142) ≤
      m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k * (10 ^ 31 - 3384) *
        (10 ^ 31 + lnErrorCoarseGePosBudgetCap) * (10 ^ 31 - 10) * 10 ^ 18) := by
  have hb := errBudgetLGe_le (k := k) hk
  have hcross : (m + 1) * Sc ≤ m * (Sc + 1) := by
    have e1 : (m + 1) * Sc = m * Sc + Sc := by
      rw [Nat.add_mul, Nat.one_mul]
    have e2 : m * (Sc + 1) = m * Sc + m := by
      rw [Nat.mul_add, Nat.mul_one]
    omega
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < Sc by decide)
  calc Sc * ((m + 1) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142))
      = ((m + 1) * Sc) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142) := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm]
    _ ≤ (m * (Sc + 1)) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142) :=
        Nat.mul_le_mul_right _ hcross
    _ = m * ((Sc + 1) * (2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142)) := by
        simp only [Nat.mul_assoc]
    _ = m * ((Sc + 1) * 2 ^ k * (10 ^ 40 : Nat) ^ k * 10 ^ 142) := by
        simp only [Nat.mul_assoc]
    _ ≤ m * (Sc * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseGePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18)) :=
        Nat.mul_le_mul_left _ (by
          simpa only [Nat.mul_assoc] using hb)
    _ = Sc * (m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ k *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseGePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18)) := by
        simp only [Nat.mul_comm, Nat.mul_left_comm]

theorem lo_ge_pos_budget_exact {m c x : Nat} {r : Int} (h1 : Sc ≤ m) (h2 : m < MHI)
    (_hc : c < 160)
    (hbudget : PosShiftGeBudgetOk m c x r) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have cap1 := capLB_lift_right (den := lnErrorBoundDen) QS_pos (x1capGeLoF h1 h2)
  have cap2LQ := capLB_lift_right (den := lnErrorBoundDen) QS_pos cap2L
  have cap2 := capLB_pow cap2LQ (160 - c)
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos capBL
  have cap12 := capLB_mul cap1 cap2
  have cap123 := capLB_mul cap12 capB
  change capLB (posPhaseNatGe m c) lnErrQ (posBaseYGe m c) (posBaseWGe c) at cap123
  have capE := capLB_first_order_self (posAvailGe m c r) lnErrQ
  have capR0 := capLB_mul cap123 capE
  have hphase : posPhaseNatGe m c ≤ lnErrArg r := hbudget.1
  have hsum : posPhaseNatGe m c + posAvailGe m c r = lnErrArg r := by
    unfold posAvailGe
    exact Nat.add_sub_of_le hphase
  rw [hsum] at capR0
  refine capLB_weaken ?_ capR0 ?_
  · unfold posBaseWGe lnErrQ QS lnErrorBoundDen
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))
      (by decide)) (by decide)
  · exact hbudget.2

theorem lo_lt_pos_budget_exact {m c x : Nat} {r : Int} (h1 : MLO ≤ m) (h2 : m < Sc)
    (_hc : c < 160)
    (hbudget : PosShiftLtBudgetOk m c x r) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have cap1 := capUB_lift_right (den := lnErrorBoundDen) QS_pos (x1capLtLoF h1 h2)
  have cap2LQ := capLB_lift_right (den := lnErrorBoundDen) QS_pos cap2L
  have cap2 := capLB_pow cap2LQ (160 - c)
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos capBL
  have hsum0 := capLB_mul cap2 capB
  change capUB (posNegXNat m) lnErrQ
    560227709747861399187319382270000000000000000000000000000000
    (m * 9999999999999999999999999996615) at cap1
  change capLB (posConstNat c) lnErrQ
    ((2 * (10 ^ 40 - 1)) ^ (160 - c) * (Sc * (10 ^ 31 - 3384)))
    (((10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31))) at hsum0
  refine capLB_cancel_first_order_budget
    (arg := lnErrArg r)
    (const := posConstNat c)
    (neg := posNegXNat m)
    (q := lnErrQ)
    (C := ((2 * (10 ^ 40 - 1)) ^ (160 - c) * (Sc * (10 ^ 31 - 3384))))
    (W := (((10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31))))
    (G := 560227709747861399187319382270000000000000000000000000000000)
    (V := m * 9999999999999999999999999996615)
    (yT := wadRayNum x)
    (wT := wadRayStrictDen)
    (by unfold lnErrQ; decide)
    hsum0 cap1 hbudget.1 hbudget.2.1 ?_ ?_ ?_
  · exact Nat.mul_pos (Nat.pow_pos (by decide)) (by decide)
  · decide
  · simpa [PosShiftLtBudgetOk, posBaseYLt, posBaseWLt, posAvailLt,
      posPhaseNatLt, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hbudget.2.2

end LnFloorCert
