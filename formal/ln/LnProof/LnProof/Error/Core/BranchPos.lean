import LnProof.Floor.CutEquiv
import LnProof.Error.Cert
import LnProof.Error.Core.CutDefs
import LnProof.Error.Core.Residue
import LnProof.Error.Core.Budget
import LnProof.Error.Core.C160

/-!
# Error bound — BranchPos

Positive-shift exact brackets for the ge and lt residue branches.
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


theorem lo_ge_pos_exact_ge_residue {m c x : Nat} {r : Int} (h1 : Sc ≤ m) (h2 : m < MHI)
    (hc1 : 1 ≤ c) (hc : c < 160)
    (hr0 : 0 ≤ r)
    (hres : PosShiftGeResidueOk m c r)
    (hxm : x < (m + 1) * 2 ^ (160 - c)) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have harg_nonneg := ln_err_arg_nonneg (by omega : -1 ≤ r)
  have hX1 := x1_nonneg_geF h1 h2
  have cap1 := capLB_lift_right (den := lnErrorBoundDen) QS_pos (x1capGeLoF h1 h2)
  have cap2LQ := capLB_lift_right (den := lnErrorBoundDen) QS_pos cap2L
  have cap2 := capLB_pow cap2LQ (160 - c)
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos capBL
  have cap12 := capLB_mul cap1 cap2
  have cap123 := capLB_mul cap12 capB
  have cap1234 := capLB_mul cap123 capECoarseGePosL
  change capLB
    (((int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
      (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
        BIASc * twoPow27N * lnErrorBoundDen) +
      (lnErrorExtraNum * twoPow99N + lnErrorCoarseGePosResidue))
    lnErrQ
      (((m * 9999999999999999999999999996615) *
        ((2 * (10 ^ 40 - 1)) ^ (160 - c))) *
        (Sc * (10 ^ 31 - 3384)) *
        (10 ^ 31 + lnErrorCoarseGePosBudgetCap))
      (((560227709747861399187319382270000000000000000000000000000000 *
        ((10 ^ 40 : Nat) ^ (160 - c))) *
        (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) at cap1234
  have hple :
      ((int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
          BIASc * twoPow27N * lnErrorBoundDen) +
        (lnErrorExtraNum * twoPow99N + lnErrorCoarseGePosResidue) ≤
      lnErrArg r := by
    apply Int.ofNat_le.mp
    have htarget : (((r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)).toNat *
        2 ^ 99 : Nat) : Int) =
        (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) * twoPow99I := by
      rw [Int.natCast_mul, Int.toNat_of_nonneg harg_nonneg]
      unfold twoPow99I
      rfl
    have hX1n : ((int256 (x1W (zWord m))).toNat : Int) =
        int256 (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
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
    have hextra : ((lnErrorExtraNum * twoPow99N : Nat) : Int) =
        (lnErrorExtraNum : Int) * twoPow99I := by
      unfold twoPow99N twoPow99I
      rfl
    have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
    have hN : (((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
        (((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I)) *
          (1000000000 : Int) := by
      rw [show (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
          ((160 - c) * (LN2c * twoPow27N)) * lnErrorBoundDen by
            simp only [Nat.mul_assoc]]
      simp only [Int.natCast_mul, hLc, hden]
    have hsum_cast :
        ((((int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
            BIASc * twoPow27N * lnErrorBoundDen) +
          (lnErrorExtraNum * twoPow99N + lnErrorCoarseGePosResidue) : Nat) : Int) =
        posPhaseI m c * (lnErrorBoundDen : Int) +
          (lnErrorExtraNum : Int) * twoPow99I +
            (lnErrorCoarseGePosResidue : Int) := by
      simp only [Int.natCast_add, Int.natCast_mul, hX1n, hBc, hN, hden,
        hextra, hscale]
      unfold posPhaseI
      generalize int256 (x1W (zWord m)) * lnPhaseScaleI = A
      generalize ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) = B
      generalize lnBiasI * twoPow27I = C
      generalize (lnErrorExtraNum : Int) * twoPow99I = E
      generalize (lnErrorCoarseGePosResidue : Int) = G
      omega
    rw [lnErrArg, htarget, hsum_cast]
    exact pos_ge_residue_arg_le_int hres
  have hmul :
      (((int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
          BIASc * twoPow27N * lnErrorBoundDen) +
        (lnErrorExtraNum * twoPow99N + lnErrorCoarseGePosResidue)) * lnErrQ ≤
      lnErrArg r * lnErrQ :=
    Nat.mul_le_mul_right _ hple
  have capR := capLB_arg (q := lnErrQ) (by unfold lnErrQ; decide) hmul cap1234
  refine capLB_weaken (p := lnErrArg r) (q := lnErrQ)
    (y := (((m * 9999999999999999999999999996615) *
      ((2 * (10 ^ 40 - 1)) ^ (160 - c))) *
      (Sc * (10 ^ 31 - 3384)) *
      (10 ^ 31 + lnErrorCoarseGePosBudgetCap)))
    (w := (((560227709747861399187319382270000000000000000000000000000000 *
      ((10 ^ 40 : Nat) ^ (160 - c))) *
      (10 ^ 18 * 10 ^ 31)) * 10 ^ 31)) ?_ capR ?_
  · have h1' : 0 < (560227709747861399187319382270000000000000000000000000000000 : Nat) *
        ((10 ^ 40 : Nat) ^ (160 - c)) := Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
    have h2' : 0 < (560227709747861399187319382270000000000000000000000000000000 : Nat) *
        ((10 ^ 40 : Nat) ^ (160 - c)) * (10 ^ 18 * 10 ^ 31) :=
      Nat.mul_pos h1' (by decide)
    exact Nat.mul_pos h2' (by decide)
  · have hb := errBudgetL_ge_fold (k := 160 - c) h1 (by omega)
    have hx1 : x + 1 ≤ (m + 1) * 2 ^ (160 - c) := by omega
    have hxw : (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) ≤
        (m + 1) * 2 ^ (160 - c) *
          (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) :=
      Nat.mul_le_mul_right _ hx1
    have hfold : (m + 1) * 2 ^ (160 - c) *
        (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) ≤
        m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseGePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18) * Sc := by
      have h := Nat.mul_le_mul_left Sc hb
      have e1 : Sc * ((m + 1) * (2 ^ (160 - c) *
          (10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) =
          (m + 1) * 2 ^ (160 - c) *
            (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have e2 : Sc * (m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseGePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18)) =
          m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
            (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseGePosBudgetCap) *
            (10 ^ 31 - 10) * 10 ^ 18) * Sc := by
        simp only [Nat.mul_comm, Nat.mul_left_comm]
      rw [e1] at h
      rw [e2] at h
      exact h
    have eL : x * 10 ^ 31 *
        (((560227709747861399187319382270000000000000000000000000000000 *
          (10 ^ 40 : Nat) ^ (160 - c)) * (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) ≤
        (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) := by
      rw [show (560227709747861399187319382270000000000000000000000000000000 : Nat) =
        Sc * 10 ^ 31 from by decide]
      have eAC : x * 10 ^ 31 *
          (((Sc * 10 ^ 31 * (10 ^ 40 : Nat) ^ (160 - c)) *
            (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) =
          x * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) *
            ((10 : Nat) ^ 31 * (10 ^ 31 * (10 ^ 18 * 10 ^ 31 * 10 ^ 31))))) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [eAC, show ((10 : Nat) ^ 31 * (10 ^ 31 * (10 ^ 18 * 10 ^ 31 * 10 ^ 31))) =
        10 ^ 142 from by decide]
      exact Nat.mul_le_mul_right _ (by omega : x ≤ x + 1)
    have eR : (((m * 9999999999999999999999999996615) *
        ((2 * (10 ^ 40 - 1)) ^ (160 - c))) *
        (Sc * (10 ^ 31 - 3384)) * (10 ^ 31 + lnErrorCoarseGePosBudgetCap)) *
        (10 ^ 18 * (10 ^ 31 - 10)) =
        m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseGePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18) * Sc := by
      rw [show (9999999999999999999999999996615 : Nat) = 10 ^ 31 - 3385 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    unfold wadRayNum wadRayStrictDen
    generalize hT1 : x * 10 ^ 31 *
      (((560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 40 : Nat) ^ (160 - c)) * (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) = T1
      at eL ⊢
    generalize hT2 : (x + 1) *
      (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) = T2 at eL hxw
    generalize hT3 : (m + 1) * 2 ^ (160 - c) *
      (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) = T3 at hxw hfold
    generalize hT4 : m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
      (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseGePosBudgetCap) *
      (10 ^ 31 - 10) * 10 ^ 18) * Sc = T4 at hfold eR
    generalize hT5 : (((m * 9999999999999999999999999996615) *
      ((2 * (10 ^ 40 - 1)) ^ (160 - c))) *
      (Sc * (10 ^ 31 - 3384)) * (10 ^ 31 + lnErrorCoarseGePosBudgetCap)) *
      (10 ^ 18 * (10 ^ 31 - 10)) = T5 at eR ⊢
    omega

theorem lo_lt_pos_exact {m c x : Nat} {r : Int} (h1 : Sc - 45 ≤ m) (h2 : m < Sc)
    (hc1 : 1 ≤ c) (hc : c < 160)
    (hrlo : r * 2 ^ 72 ≤ int256 (x1W (zWord m)) * 7450580596923828125 +
      ln2kInt c + 116873961749927929127912020551560854268589826112230)
    (hr0 : 0 ≤ r)
    (hres : PosShiftResidueOk m c r)
    (hxm : x < (m + 1) * 2 ^ (160 - c)) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have hmlo : MLO ≤ m := Nat.le_trans (by decide : MLO ≤ Sc - 45) h1
  have harg_nonneg := ln_err_arg_nonneg (by omega : -1 ≤ r)
  have cap1 := capUB_lift_right (den := lnErrorBoundDen) QS_pos (x1capLtLoF hmlo h2)
  have cap2LQ := capLB_lift_right (den := lnErrorBoundDen) QS_pos cap2L
  have cap2 := capLB_pow cap2LQ (160 - c)
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos capBL
  have cap2B := capLB_mul cap2 capB
  have hsum := capLB_mul cap2B capECoarsePosL
  have hX1 := x1_nonpos_ltF hmlo h2
  have hVs := v_scale_pos (int256 (x1W (zWord m))) c (by omega : c ≤ 160)
  have hV0 : 0 ≤ (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551560854268589826112230) * 2 ^ 27 := by
    have h0 : 0 ≤ r * 2 ^ 72 := Int.mul_nonneg hr0 (by decide)
    have hg : 0 ≤ int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551560854268589826112230 := by
      generalize hgV : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551560854268589826112230 = V at hrlo ⊢
      generalize hgR : r * 2 ^ 72 = R at hrlo h0
      omega
    exact Int.mul_nonneg hg (by decide)
  change capUB ((-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen)
    lnErrQ 560227709747861399187319382270000000000000000000000000000000
      (m * 9999999999999999999999999996615) at cap1
  change capLB
    (((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
      BIASc * twoPow27N * lnErrorBoundDen) +
      (lnErrorExtraNum * twoPow99N + lnErrorCoarsePosResidue))
    lnErrQ
      (((2 * (10 ^ 40 - 1)) ^ (160 - c) * (Sc * (10 ^ 31 - 3384))) *
        (10 ^ 31 + lnErrorCoarsePosBudgetCap))
      ((((10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31)) * 10 ^ 31)) at hsum
  have hnegXn : (((-int256 (x1W (zWord m))).toNat : Nat) : Int) =
      -int256 (x1W (zWord m)) :=
    Int.toNat_of_nonneg (by omega)
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
  have hextra : ((lnErrorExtraNum * twoPow99N : Nat) : Int) =
      (lnErrorExtraNum : Int) * twoPow99I := by
    unfold twoPow99N twoPow99I
    rfl
  have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
  have hN : (((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
      (((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I)) *
        (1000000000 : Int) := by
    rw [show (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
        ((160 - c) * (LN2c * twoPow27N)) * lnErrorBoundDen by
          simp only [Nat.mul_assoc]]
    simp only [Int.natCast_mul, hLc, hden]
  have hVsI :
      (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
          lnBiasI) * twoPow27I = posPhaseI m c := by
    unfold posPhaseI
    simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
  have hV0I : 0 ≤ posPhaseI m c := by
    have hV0' : 0 ≤ (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        lnBiasI) * twoPow27I := by
      simpa [lnBiasI, twoPow27I] using hV0
    rw [hVsI] at hV0'
    exact hV0'
  have hcancel_le :
      (-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen ≤
        ((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
          BIASc * twoPow27N * lnErrorBoundDen) +
          (lnErrorExtraNum * twoPow99N + lnErrorCoarsePosResidue) := by
    apply Int.ofNat_le.mp
    simp only [Int.natCast_add, Int.natCast_mul, hnegXn, hBc, hN, hden, hextra, hscale]
    have hmain : (-int256 (x1W (zWord m))) * lnPhaseScaleI ≤
        ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
          lnBiasI * twoPow27I := by
      unfold posPhaseI at hV0I
      rw [Int.neg_mul]
      generalize int256 (x1W (zWord m)) * lnPhaseScaleI = A at hV0I ⊢
      generalize ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) = B at hV0I ⊢
      generalize lnBiasI * twoPow27I = C at hV0I ⊢
      omega
    have hmul := Int.mul_le_mul_of_nonneg_right hmain (by decide : 0 ≤ (1000000000 : Int))
    have hmul' : (-int256 (x1W (zWord m))) * lnPhaseScaleI * (1000000000 : Int) ≤
        ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) * (1000000000 : Int) +
          lnBiasI * twoPow27I * (1000000000 : Int) := by
      have e : (((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
          lnBiasI * twoPow27I) * (1000000000 : Int) =
          ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) * (1000000000 : Int) +
            lnBiasI * twoPow27I * (1000000000 : Int) := by
        rw [Int.add_mul]
      rw [e] at hmul
      exact hmul
    have hnon : 0 ≤ (lnErrorExtraNum : Int) * twoPow99I +
        (lnErrorCoarsePosResidue : Int) := by
      have hE : 0 ≤ (lnErrorExtraNum : Int) * twoPow99I := by
        unfold twoPow99I
        exact Int.mul_nonneg (Int.natCast_nonneg _) (by decide)
      exact Int.add_nonneg hE (Int.natCast_nonneg _)
    exact Int.le_trans hmul' (Int.le_add_of_nonneg_right hnon)
  have hsplit :
      ((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
        BIASc * twoPow27N * lnErrorBoundDen) +
        (lnErrorExtraNum * twoPow99N + lnErrorCoarsePosResidue) =
      (((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
        BIASc * twoPow27N * lnErrorBoundDen) +
        (lnErrorExtraNum * twoPow99N + lnErrorCoarsePosResidue) -
          (-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen) +
        (-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen := by
    exact (Nat.sub_add_cancel hcancel_le).symm
  rw [hsplit] at hsum
  have capV := capLB_cancel (q := lnErrQ) (by unfold lnErrQ; decide) hsum cap1
  have hple :
      ((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
        BIASc * twoPow27N * lnErrorBoundDen) +
        (lnErrorExtraNum * twoPow99N + lnErrorCoarsePosResidue) -
          (-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen ≤
      lnErrArg r := by
    apply Int.ofNat_le.mp
    have htarget : (((r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)).toNat *
        2 ^ 99 : Nat) : Int) =
        (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) * twoPow99I := by
      rw [Int.natCast_mul, Int.toNat_of_nonneg harg_nonneg]
      unfold twoPow99I
      rfl
    have hsub_cast :
        (((((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
          BIASc * twoPow27N * lnErrorBoundDen) +
          (lnErrorExtraNum * twoPow99N + lnErrorCoarsePosResidue) -
            (-int256 (x1W (zWord m))).toNat * lnPhaseScaleN *
              lnErrorBoundDen : Nat) : Int)) =
        posPhaseI m c * (lnErrorBoundDen : Int) +
          (lnErrorExtraNum : Int) * twoPow99I +
            (lnErrorCoarsePosResidue : Int) := by
      have hsI := congrArg (fun n : Nat => ((n : Nat) : Int)) hsplit
      simp only [Int.natCast_add, Int.natCast_mul, hnegXn, hBc, hN, hden,
        hextra, hscale] at hsI
      rw [show -int256 (x1W (zWord m)) * lnPhaseScaleI =
          -(int256 (x1W (zWord m)) * lnPhaseScaleI) by rw [Int.neg_mul]] at hsI
      generalize (((((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
        BIASc * twoPow27N * lnErrorBoundDen) +
        (lnErrorExtraNum * twoPow99N + lnErrorCoarsePosResidue) -
          (-int256 (x1W (zWord m))).toNat * lnPhaseScaleN *
            lnErrorBoundDen : Nat) : Int)) = S at hsI ⊢
      unfold posPhaseI
      rw [hden]
      generalize int256 (x1W (zWord m)) * lnPhaseScaleI = A at hsI ⊢
      generalize ((160 - c : Nat) : Int) * ((LN2c : Int) * twoPow27I) = L at hsI ⊢
      generalize lnBiasI * twoPow27I = B at hsI ⊢
      generalize (lnErrorExtraNum : Int) * twoPow99I = E at hsI ⊢
      generalize (lnErrorCoarsePosResidue : Int) = G at hsI ⊢
      omega
    rw [lnErrArg, htarget, hsub_cast]
    exact pos_residue_arg_le_int hres
  have hmul :
      (((160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
        BIASc * twoPow27N * lnErrorBoundDen) +
        (lnErrorExtraNum * twoPow99N + lnErrorCoarsePosResidue) -
          (-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen) * lnErrQ ≤
      lnErrArg r * lnErrQ :=
    Nat.mul_le_mul_right _ hple
  have capR := capLB_arg (q := lnErrQ) (by unfold lnErrQ; decide) hmul capV
  refine capLB_weaken (p := lnErrArg r) (q := lnErrQ)
    (y := ((((2 * (10 ^ 40 - 1)) ^ (160 - c) * (Sc * (10 ^ 31 - 3384))) *
      (10 ^ 31 + lnErrorCoarsePosBudgetCap)) *
      (m * 9999999999999999999999999996615)))
    (w := ((((10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31)) *
      10 ^ 31) *
      560227709747861399187319382270000000000000000000000000000000)) ?_ capR ?_
  · have h1' : 0 < (((10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31)) *
        10 ^ 31 : Nat) :=
      Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by decide)) (by decide)) (by decide)
    exact Nat.mul_pos h1' (by decide)
  · have hMLO : Sc - 45 ≤ m := h1
    have hb := errBudgetL_fold (k := 160 - c) hMLO (by omega)
    have hx1 : x + 1 ≤ (m + 1) * 2 ^ (160 - c) := by omega
    have hxw : (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) ≤
        (m + 1) * 2 ^ (160 - c) *
          (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) :=
      Nat.mul_le_mul_right _ hx1
    have hfold : (m + 1) * 2 ^ (160 - c) *
        (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) ≤
        m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarsePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18) * Sc := by
      have h := Nat.mul_le_mul_left Sc hb
      have e1 : Sc * ((m + 1) * (2 ^ (160 - c) *
          (10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) =
          (m + 1) * 2 ^ (160 - c) *
            (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have e2 : Sc * (m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarsePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18)) =
          m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
            (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarsePosBudgetCap) *
            (10 ^ 31 - 10) * 10 ^ 18) * Sc := by
        simp only [Nat.mul_comm, Nat.mul_left_comm]
      rw [e1] at h
      rw [e2] at h
      exact h
    have eL : x * 10 ^ 31 * ((((10 ^ 40 : Nat) ^ (160 - c) *
        (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) *
        560227709747861399187319382270000000000000000000000000000000) ≤
        (x + 1) * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) := by
      rw [show (560227709747861399187319382270000000000000000000000000000000 : Nat) =
        Sc * 10 ^ 31 from by decide]
      have eAC : x * 10 ^ 31 * ((((10 ^ 40 : Nat) ^ (160 - c) *
          (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) * (Sc * 10 ^ 31)) =
          x * (Sc * ((10 ^ 40 : Nat) ^ (160 - c) *
            ((10 : Nat) ^ 18 * ((10 : Nat) ^ 31 *
              ((10 : Nat) ^ 31 * ((10 : Nat) ^ 31 * (10 : Nat) ^ 31)))))) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [eAC, show ((10 : Nat) ^ 18 * ((10 : Nat) ^ 31 *
        ((10 : Nat) ^ 31 * ((10 : Nat) ^ 31 * (10 : Nat) ^ 31)))) = 10 ^ 142
        from by decide]
      exact Nat.mul_le_mul_right _ (by omega : x ≤ x + 1)
    have eR : ((((2 * (10 ^ 40 - 1)) ^ (160 - c) * (Sc * (10 ^ 31 - 3384))) *
        (10 ^ 31 + lnErrorCoarsePosBudgetCap)) *
        (m * 9999999999999999999999999996615)) *
        (10 ^ 18 * (10 ^ 31 - 10)) =
        m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarsePosBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18) * Sc := by
      rw [show (9999999999999999999999999996615 : Nat) = 10 ^ 31 - 3385 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    unfold wadRayNum wadRayStrictDen
    generalize hT1 : x * 10 ^ 31 * ((((10 ^ 40 : Nat) ^ (160 - c) *
      (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) *
      560227709747861399187319382270000000000000000000000000000000) = T1 at eL ⊢
    generalize hT2 : (x + 1) *
      (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) = T2 at eL hxw
    generalize hT3 : (m + 1) * 2 ^ (160 - c) *
      (Sc * ((10 ^ 40 : Nat) ^ (160 - c) * 10 ^ 142)) = T3 at hxw hfold
    generalize hT4 : m * ((10 ^ 31 - 3385) * (2 * (10 ^ 40 - 1)) ^ (160 - c) *
      (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarsePosBudgetCap) *
      (10 ^ 31 - 10) * 10 ^ 18) * Sc = T4 at hfold eR
    generalize hT5 : ((((2 * (10 ^ 40 - 1)) ^ (160 - c) *
      (Sc * (10 ^ 31 - 3384))) * (10 ^ 31 + lnErrorCoarsePosBudgetCap)) *
      (m * 9999999999999999999999999996615)) *
      (10 ^ 18 * (10 ^ 31 - 10)) = T5 at eR ⊢
    omega

end LnFloorCert
