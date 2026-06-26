import LnProof.Floor.CutEquiv
import LnProof.Error.Cert
import LnProof.Error.Core.CutDefs
import LnProof.Error.Core.Args
import LnProof.Error.Core.C160

/-!
# Error bound — BranchNeg

Negative-output exact brackets: `lo_ge_neg_exact`, `lo_lt_neg_exact`.
-/

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

namespace LnFloorCert

open LnYul LnFloor LnExp LnPoly

attribute [local irreducible] lnWadToRayBody


theorem lo_ge_neg_exact {m c x : Nat} {r : Int} (h1 : Sc ≤ m) (h2 : m < MHI)
    (hc : 160 < c) (hc2 : c ≤ 255)
    (hr : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551516284764321243411868 < (r + 1) * 2 ^ 72)
    (hrlo : r * 2 ^ 72 ≤ int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551516284764321243411868)
    (hr0 : 0 ≤ r)
    (hmx : m = x * 2 ^ (c - 160)) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have harg_nonneg := ln_err_arg_nonneg (by omega : -1 ≤ r)
  have cap1 := capLB_lift_right (den := lnErrorBoundDen) QS_pos (x1capGeLoF h1 h2)
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos capBL
  have cap1B := capLB_mul cap1 capB
  have cap1BE := capLB_mul cap1B capECoarseNegL
  have cap2UQ := capUB_lift_right (den := lnErrorBoundDen) QS_pos cap2U
  have cap2 := capUB_pow (by unfold QS lnErrorBoundDen; decide) cap2UQ (c - 160)
  have hX1 := x1_nonneg_geF h1 h2
  have hVs := v_scale_neg (int256 (x1W (zWord m))) c hc
  have hV0 : 0 ≤ (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551516284764321243411868) * 2 ^ 27 := by
    have h0 : 0 ≤ r * 2 ^ 72 := Int.mul_nonneg hr0 (by decide)
    have hg : 0 ≤ int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551516284764321243411868 := by
      generalize hgV : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551516284764321243411868 = V at hrlo ⊢
      generalize hgR : r * 2 ^ 72 = R at hrlo h0
      omega
    exact Int.mul_nonneg hg (by decide)
  change capLB ((int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
      BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N)
    lnErrQ
      ((m * 9999999999999999999999999996615) * (Sc * (10 ^ 31 - 3384)) *
        (10 ^ 31 + lnErrorCoarseNegBudgetCap))
      ((560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) at cap1BE
  have hcancel_le : (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) ≤
      (int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N := by
    apply Int.ofNat_le.mp
    have hX1n : ((int256 (x1W (zWord m))).toNat : Int) = int256 (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
      unfold twoPow27N twoPow27I lnBiasI
      decide +kernel
    have hLc : (((c - 160) * (LN2c * twoPow27N) : Nat) : Int) =
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) := by
      simp only [Int.natCast_mul]
      unfold twoPow27N twoPow27I
      rfl
    have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
      unfold lnErrorBoundDen
      rfl
    have hextra : ((lnErrorExtraNum * twoPow99N : Nat) : Int) =
        698600000 * twoPow99I := by
      unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen twoPow99N twoPow99I
      decide +kernel
    have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
    have hV0I : 0 ≤ (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        lnBiasI) * twoPow27I := by
      simpa [lnBiasI, twoPow27I] using hV0
    have hVsI :
        (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
            lnBiasI) * twoPow27I +
          ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) =
        int256 (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I := by
      simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
    generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI) * twoPow27I = V27 at hV0I hVsI
    generalize hgA : int256 (x1W (zWord m)) * lnPhaseScaleI = A at hVsI
    generalize hgB : ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = B at hVsI hLc
    generalize hgC : (c - 160) * (LN2c * twoPow27N) = Cn at hLc ⊢
    generalize hgD : (int256 (x1W (zWord m))).toNat * lnPhaseScaleN = D at ⊢
    have hAD : (D : Int) = A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n, hscale]
    generalize hgE : BIASc * twoPow27N = E at hBc ⊢
    generalize hgX : lnErrorExtraNum * twoPow99N = Ex at hextra ⊢
    have hN : (((c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
        B * (1000000000 : Int) := by
      rw [show (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
          Cn * lnErrorBoundDen by
            rw [← hgC]
            simp only [Nat.mul_assoc]]
      simp only [Int.natCast_mul, hLc, hden]
    clear hX1n hX1 cap1 capB cap1B cap1BE cap2UQ cap2 hr h1 h2 hc hc2 hmx hrlo hVs
    simp only [Int.natCast_add, Int.natCast_mul, hden, hAD, hBc, hextra, hN]
    omega
  have hsplit : (int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
      BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N =
      ((int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
          (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen)) +
        (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) := by
    exact (Nat.sub_add_cancel hcancel_le).symm
  rw [hsplit] at cap1BE
  have capV := capLB_cancel (q := lnErrQ) (by unfold lnErrQ; decide) cap1BE cap2
  have hple : (int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
      BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
        (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) ≤
      lnErrArg r := by
    apply Int.ofNat_le.mp
    have htarget : (((r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)).toNat *
        2 ^ 99 : Nat) : Int) =
        (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) * twoPow99I := by
      rw [Int.natCast_mul, Int.toNat_of_nonneg harg_nonneg]
      unfold twoPow99I
      rfl
    have hX1n : ((int256 (x1W (zWord m))).toNat : Int) = int256 (x1W (zWord m)) :=
      Int.toNat_of_nonneg hX1
    have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
      unfold twoPow27N twoPow27I lnBiasI
      decide +kernel
    have hLc : (((c - 160) * (LN2c * twoPow27N) : Nat) : Int) =
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) := by
      simp only [Int.natCast_mul]
      unfold twoPow27N twoPow27I
      rfl
    have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
      unfold lnErrorBoundDen
      rfl
    have hextra : ((lnErrorExtraNum * twoPow99N : Nat) : Int) =
        698600000 * twoPow99I := by
      unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen twoPow99N twoPow99I
      decide +kernel
    have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
    have hsub_cast :
        (((int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
            (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
        (int256 (x1W (zWord m)) * lnPhaseScaleI -
            ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
            lnBiasI * twoPow27I) * (1000000000 : Int) +
          698600000 * twoPow99I := by
      have hsI := congrArg (fun n : Nat => ((n : Nat) : Int)) hsplit
      have hN : (((c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
          (((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I)) *
            (1000000000 : Int) := by
        rw [show (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
            ((c - 160) * (LN2c * twoPow27N)) * lnErrorBoundDen by
              simp only [Nat.mul_assoc]]
        simp only [Int.natCast_mul, hLc, hden]
      simp only [Int.natCast_add, Int.natCast_mul, hX1n, hBc, hN, hden,
        hextra, hscale] at hsI
      generalize (((int256 (x1W (zWord m))).toNat * lnPhaseScaleN *
        lnErrorBoundDen + BIASc * twoPow27N * lnErrorBoundDen +
        lnErrorExtraNum * twoPow99N -
        (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) = S at hsI ⊢
      generalize int256 (x1W (zWord m)) * lnPhaseScaleI = A at hsI ⊢
      generalize ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = B at hsI ⊢
      generalize lnBiasI * twoPow27I = C at hsI ⊢
      generalize 698600000 * twoPow99I = E at hsI ⊢
      omega
    rw [lnErrArg, htarget, hsub_cast]
    have hsc : int256 (x1W (zWord m)) * lnPhaseScaleI -
          ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
          lnBiasI * twoPow27I ≤
        (r + 1) * twoPow99I - twoPow27I := by
      have h := phase_lt_scaled_le (V := int256 (x1W (zWord m)) *
          7450580596923828125 + ln2kInt c + lnBiasI)
        (T := (r + 1) * twoPow72I) (by simpa [lnBiasI, twoPow72I] using hr)
      change (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
          lnBiasI) * twoPow27I ≤ ((r + 1) * twoPow72I - 1) * twoPow27I at h
      have er : ((r + 1) * twoPow72I - 1) * twoPow27I =
          (r + 1) * twoPow99I - twoPow27I := by
        unfold twoPow72I twoPow27I twoPow99I
        rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
          by decide]
        omega
      rw [er] at h
      have hVsI :
          (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
              lnBiasI) * twoPow27I +
            ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) =
          int256 (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I := by
        simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
      generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 +
        ln2kInt c + lnBiasI) * twoPow27I = V27 at h hVsI
      generalize hgL : ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = L at hVsI ⊢
      generalize hgA : int256 (x1W (zWord m)) * lnPhaseScaleI = A at hVsI ⊢
      generalize hgB : lnBiasI * twoPow27I = B at hVsI ⊢
      omega
    have hcore := c160_arg_le_int (A :=
      int256 (x1W (zWord m)) * lnPhaseScaleI -
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
        lnBiasI * twoPow27I) (r := r) hsc
    simpa [lnErrorBoundDen, lnErrorBoundNum, twoPow99I] using hcore
  have hmul :
      ((int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
          (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen)) * lnErrQ ≤
        lnErrArg r * lnErrQ :=
    Nat.mul_le_mul_right _ hple
  have capR : capLB (lnErrArg r) lnErrQ
      (((m * 9999999999999999999999999996615) * (Sc * (10 ^ 31 - 3384)) *
        (10 ^ 31 + lnErrorCoarseNegBudgetCap)) * (10 ^ 40) ^ (c - 160))
      ((((560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) * (2 * (10 ^ 40 + 1)) ^ (c - 160))) :=
    @capLB_arg
      (lnErrArg r) lnErrQ
      ((int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
          (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen))
      lnErrQ
      (((m * 9999999999999999999999999996615) * (Sc * (10 ^ 31 - 3384)) *
        (10 ^ 31 + lnErrorCoarseNegBudgetCap)) * (10 ^ 40) ^ (c - 160))
      ((((560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) * (2 * (10 ^ 40 + 1)) ^ (c - 160)))
      (by unfold lnErrQ; decide) hmul capV
  refine capLB_weaken (p := lnErrArg r) (q := lnErrQ)
    (y := (((m * 9999999999999999999999999996615) * (Sc * (10 ^ 31 - 3384)) *
      (10 ^ 31 + lnErrorCoarseNegBudgetCap)) * (10 ^ 40) ^ (c - 160)))
    (w := ((((560227709747861399187319382270000000000000000000000000000000 *
      (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) * (2 * (10 ^ 40 + 1)) ^ (c - 160))))
    ?_ capR ?_
  · have h1' : 0 < (560227709747861399187319382270000000000000000000000000000000 : Nat) *
        (10 ^ 18 * 10 ^ 31) * 10 ^ 31 := by decide
    exact Nat.mul_pos h1' (Nat.pow_pos (by decide))
  · have hb := errBudgetLn_le (j := c - 160) (by omega)
    have hbf := Nat.mul_le_mul_left (x * Sc) hb
    have eL : x * 10 ^ 31 *
        (((560227709747861399187319382270000000000000000000000000000000 *
          (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) * (2 * (10 ^ 40 + 1)) ^ (c - 160)) =
        x * Sc * ((10 : Nat) ^ 142 * (2 * (10 ^ 40 + 1)) ^ (c - 160)) := by
      rw [show (560227709747861399187319382270000000000000000000000000000000 : Nat) =
        Sc * 10 ^ 31 from by decide]
      have e' : ∀ P : Nat, (10 : Nat) ^ 18 * ((10 : Nat) ^ 31 * ((10 : Nat) ^ 31 *
          ((10 : Nat) ^ 31 * ((10 : Nat) ^ 31 * P)))) = (10 : Nat) ^ 142 * P := by
        intro P
        rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc,
          show ((10 : Nat) ^ 18 * 10 ^ 31 * 10 ^ 31 * 10 ^ 31 * 10 ^ 31) = 10 ^ 142
            from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e' ((2 * (10 ^ 40 + 1)) ^ (c - 160))]
    have eR : (((m * 9999999999999999999999999996615) * (Sc * (10 ^ 31 - 3384)) *
        (10 ^ 31 + lnErrorCoarseNegBudgetCap)) * (10 ^ 40 : Nat) ^ (c - 160)) *
        (10 ^ 18 * (10 ^ 31 - 10)) =
        x * Sc * (2 ^ (c - 160) * (10 ^ 40 : Nat) ^ (c - 160) * (10 ^ 31 - 3385) *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18) := by
      rw [hmx, show (9999999999999999999999999996615 : Nat) = 10 ^ 31 - 3385 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    unfold wadRayNum wadRayStrictDen
    generalize hT1 : x * 10 ^ 31 *
      (((560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) * (2 * (10 ^ 40 + 1)) ^ (c - 160)) = T1
      at eL ⊢
    generalize hT2 : x * Sc * ((10 : Nat) ^ 142 * (2 * (10 ^ 40 + 1)) ^ (c - 160)) = T2
      at eL hbf
    generalize hT3 : x * Sc * (2 ^ (c - 160) * (10 ^ 40 : Nat) ^ (c - 160) *
      (10 ^ 31 - 3385) * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap) *
      (10 ^ 31 - 10) * 10 ^ 18) = T3 at eR hbf
    generalize hT4 : (((m * 9999999999999999999999999996615) * (Sc * (10 ^ 31 - 3384)) *
      (10 ^ 31 + lnErrorCoarseNegBudgetCap)) * (10 ^ 40 : Nat) ^ (c - 160)) *
      (10 ^ 18 * (10 ^ 31 - 10)) = T4 at eR ⊢
    omega

theorem lo_lt_neg_exact {m c x : Nat} {r : Int} (h1 : MLO ≤ m) (h2 : m < Sc)
    (hc : 160 < c) (hc2 : c ≤ 255)
    (hr : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551516284764321243411868 < (r + 1) * 2 ^ 72)
    (hrlo : r * 2 ^ 72 ≤ int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551516284764321243411868)
    (hr0 : 0 ≤ r)
    (hmx : m = x * 2 ^ (c - 160)) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have harg_nonneg := ln_err_arg_nonneg (by omega : -1 ≤ r)
  have cap1 := capUB_lift_right (den := lnErrorBoundDen) QS_pos (x1capLtLoF h1 h2)
  have cap2UQ := capUB_lift_right (den := lnErrorBoundDen) QS_pos cap2U
  have hb := capUB_mul (by unfold QS lnErrorBoundDen; decide) cap1
    (capUB_pow (by unfold QS lnErrorBoundDen; decide) cap2UQ (c - 160))
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos capBL
  have hsum := capLB_mul capB capECoarseNegL
  have hX1 := x1_nonpos_ltF h1 h2
  have hVs := v_scale_neg (int256 (x1W (zWord m))) c hc
  have hV0 : 0 ≤ (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551516284764321243411868) * 2 ^ 27 := by
    have h0 : 0 ≤ r * 2 ^ 72 := Int.mul_nonneg hr0 (by decide)
    have hg : 0 ≤ int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551516284764321243411868 := by
      generalize hgV : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551516284764321243411868 = V at hrlo ⊢
      generalize hgR : r * 2 ^ 72 = R at hrlo h0
      omega
    exact Int.mul_nonneg hg (by decide)
  change capUB (((-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen) +
      (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen))
    lnErrQ
      (560227709747861399187319382270000000000000000000000000000000 *
        ((2 * (10 ^ 40 + 1)) ^ (c - 160)))
      ((m * 9999999999999999999999999996615) * ((10 ^ 40) ^ (c - 160))) at hb
  change capLB (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N)
    lnErrQ (Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap))
      ((10 ^ 18 * 10 ^ 31) * 10 ^ 31) at hsum
  have hcancel_le :
      (-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) ≤
      BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N := by
    apply Int.ofNat_le.mp
    have hX1n : (((-int256 (x1W (zWord m))).toNat : Nat) : Int) =
        -int256 (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
      unfold twoPow27N twoPow27I lnBiasI
      decide +kernel
    have hLc : (((c - 160) * (LN2c * twoPow27N) : Nat) : Int) =
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) := by
      simp only [Int.natCast_mul]
      unfold twoPow27N twoPow27I
      rfl
    have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
      unfold lnErrorBoundDen
      rfl
    have hextra : ((lnErrorExtraNum * twoPow99N : Nat) : Int) =
        698600000 * twoPow99I := by
      unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen twoPow99N twoPow99I
      decide +kernel
    have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
    have hV0I : 0 ≤ (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        lnBiasI) * twoPow27I := by
      simpa [lnBiasI, twoPow27I] using hV0
    have hVsI :
        (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
            lnBiasI) * twoPow27I +
          ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) =
        int256 (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I := by
      simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
    generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI) * twoPow27I = V27 at hV0I hVsI
    generalize hgA : int256 (x1W (zWord m)) * lnPhaseScaleI = A at hVsI
    generalize hgB : ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = B at hVsI hLc
    generalize hgC : (c - 160) * (LN2c * twoPow27N) = Cn at hLc ⊢
    generalize hgD : (-int256 (x1W (zWord m))).toNat * lnPhaseScaleN = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n, hscale]
      rw [Int.neg_mul]
    generalize hgE : BIASc * twoPow27N = E at hBc ⊢
    generalize hgX : lnErrorExtraNum * twoPow99N = Ex at hextra ⊢
    have hN : (((c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
        B * (1000000000 : Int) := by
      rw [show (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
          Cn * lnErrorBoundDen by
            rw [← hgC]
            simp only [Nat.mul_assoc]]
      simp only [Int.natCast_mul, hLc, hden]
    clear hX1n hX1 cap1 cap2UQ hb capB hsum hr h1 h2 hc hc2 hmx hrlo hVs
    simp only [Int.natCast_add, Int.natCast_mul, hden, hAD, hBc, hextra, hN]
    omega
  have hsplit : BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N =
      (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
        ((-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen))) +
        ((-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen)) := by
    exact (Nat.sub_add_cancel hcancel_le).symm
  rw [hsplit] at hsum
  have capV := capLB_cancel (q := lnErrQ) (by unfold lnErrQ; decide) hsum hb
  have hple : BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
      ((-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen)) ≤
      lnErrArg r := by
    apply Int.ofNat_le.mp
    have htarget : (((r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)).toNat *
        2 ^ 99 : Nat) : Int) =
        (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) * twoPow99I := by
      rw [Int.natCast_mul, Int.toNat_of_nonneg harg_nonneg]
      unfold twoPow99I
      rfl
    have hX1n : (((-int256 (x1W (zWord m))).toNat : Nat) : Int) =
        -int256 (x1W (zWord m)) :=
      Int.toNat_of_nonneg (by omega)
    have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
      unfold twoPow27N twoPow27I lnBiasI
      decide +kernel
    have hLc : (((c - 160) * (LN2c * twoPow27N) : Nat) : Int) =
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) := by
      simp only [Int.natCast_mul]
      unfold twoPow27N twoPow27I
      rfl
    have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
      unfold lnErrorBoundDen
      rfl
    have hextra : ((lnErrorExtraNum * twoPow99N : Nat) : Int) =
        698600000 * twoPow99I := by
      unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen twoPow99N twoPow99I
      decide +kernel
    have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
    have hN : (((c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
        (((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I)) *
          (1000000000 : Int) := by
      rw [show (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
          ((c - 160) * (LN2c * twoPow27N)) * lnErrorBoundDen by
            simp only [Nat.mul_assoc]]
      simp only [Int.natCast_mul, hLc, hden]
    have hsub_cast :
        (((BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
          ((-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
            (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen)) : Nat) : Int)) =
        (int256 (x1W (zWord m)) * lnPhaseScaleI -
            ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
            lnBiasI * twoPow27I) * (1000000000 : Int) +
          698600000 * twoPow99I := by
      have hsI := congrArg (fun n : Nat => ((n : Nat) : Int)) hsplit
      simp only [Int.natCast_add, Int.natCast_mul, hX1n, hBc, hN, hden,
        hextra, hscale] at hsI
      rw [show -int256 (x1W (zWord m)) * lnPhaseScaleI =
          -(int256 (x1W (zWord m)) * lnPhaseScaleI) by rw [Int.neg_mul]] at hsI
      generalize (((BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum *
        twoPow99N - ((-int256 (x1W (zWord m))).toNat * lnPhaseScaleN *
        lnErrorBoundDen + (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen)) : Nat) : Int)) = S
        at hsI ⊢
      generalize int256 (x1W (zWord m)) * lnPhaseScaleI = A at hsI ⊢
      generalize ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = B at hsI ⊢
      generalize lnBiasI * twoPow27I = C at hsI ⊢
      generalize 698600000 * twoPow99I = E at hsI ⊢
      omega
    rw [lnErrArg, htarget, hsub_cast]
    have hsc : int256 (x1W (zWord m)) * lnPhaseScaleI -
          ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
          lnBiasI * twoPow27I ≤
        (r + 1) * twoPow99I - twoPow27I := by
      have h := phase_lt_scaled_le (V := int256 (x1W (zWord m)) *
          7450580596923828125 + ln2kInt c + lnBiasI)
        (T := (r + 1) * twoPow72I) (by simpa [lnBiasI, twoPow72I] using hr)
      change (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
          lnBiasI) * twoPow27I ≤ ((r + 1) * twoPow72I - 1) * twoPow27I at h
      have er : ((r + 1) * twoPow72I - 1) * twoPow27I =
          (r + 1) * twoPow99I - twoPow27I := by
        unfold twoPow72I twoPow27I twoPow99I
        rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
          by decide]
        omega
      rw [er] at h
      have hVsI :
          (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
              lnBiasI) * twoPow27I +
            ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) =
          int256 (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I := by
        simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
      generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 +
        ln2kInt c + lnBiasI) * twoPow27I = V27 at h hVsI
      generalize hgL : ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = L at hVsI ⊢
      generalize hgA : int256 (x1W (zWord m)) * lnPhaseScaleI = A at hVsI ⊢
      generalize hgB : lnBiasI * twoPow27I = B at hVsI ⊢
      omega
    have hcore := c160_arg_le_int (A :=
      int256 (x1W (zWord m)) * lnPhaseScaleI -
        ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
        lnBiasI * twoPow27I) (r := r) hsc
    simpa [lnErrorBoundDen, lnErrorBoundNum, twoPow99I] using hcore
  have hmul : (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
      ((-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen))) * lnErrQ ≤
      lnErrArg r * lnErrQ :=
    Nat.mul_le_mul_right _ hple
  have capR : capLB (lnErrArg r) lnErrQ
      ((Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap)) *
        (m * 9999999999999999999999999996615 * (10 ^ 40 : Nat) ^ (c - 160)))
      (((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
        (560227709747861399187319382270000000000000000000000000000000 *
          (2 * (10 ^ 40 + 1)) ^ (c - 160))) :=
    @capLB_arg
      (lnErrArg r) lnErrQ
      (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
        ((-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen)))
      lnErrQ
      ((Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap)) *
        (m * 9999999999999999999999999996615 * (10 ^ 40 : Nat) ^ (c - 160)))
      (((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
        (560227709747861399187319382270000000000000000000000000000000 *
          (2 * (10 ^ 40 + 1)) ^ (c - 160)))
      (by unfold lnErrQ; decide) hmul capV
  refine capLB_weaken (p := lnErrArg r) (q := lnErrQ)
    (y := ((Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap)) *
      (m * 9999999999999999999999999996615 * (10 ^ 40 : Nat) ^ (c - 160))))
    (w := (((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
      (560227709747861399187319382270000000000000000000000000000000 *
        (2 * (10 ^ 40 + 1)) ^ (c - 160))))
    ?_ capR ?_
  · have h1' : 0 < ((10 ^ 18 * 10 ^ 31) * 10 ^ 31 : Nat) := by decide
    exact Nat.mul_pos h1' (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))
  · have hbg := errBudgetLn_le (j := c - 160) (by omega)
    have hbf := Nat.mul_le_mul_left (x * Sc) hbg
    have eL : x * 10 ^ 31 * (((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
        (560227709747861399187319382270000000000000000000000000000000 *
          (2 * (10 ^ 40 + 1)) ^ (c - 160))) =
        x * Sc * ((10 : Nat) ^ 142 * (2 * (10 ^ 40 + 1)) ^ (c - 160)) := by
      rw [show (560227709747861399187319382270000000000000000000000000000000 : Nat) =
        Sc * 10 ^ 31 from by decide]
      have e' : ∀ P : Nat, (10 : Nat) ^ 18 * ((10 : Nat) ^ 31 * ((10 : Nat) ^ 31 *
          ((10 : Nat) ^ 31 * ((10 : Nat) ^ 31 * P)))) = (10 : Nat) ^ 142 * P := by
        intro P
        rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.mul_assoc,
          show ((10 : Nat) ^ 18 * 10 ^ 31 * 10 ^ 31 * 10 ^ 31 * 10 ^ 31) = 10 ^ 142
            from by decide]
      have eAC : x * 10 ^ 31 * (((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
          (Sc * 10 ^ 31 * (2 * (10 ^ 40 + 1)) ^ (c - 160))) =
          x * (Sc * ((10 : Nat) ^ 18 * ((10 : Nat) ^ 31 * ((10 : Nat) ^ 31 *
            ((10 : Nat) ^ 31 * ((10 : Nat) ^ 31 *
              (2 * (10 ^ 40 + 1)) ^ (c - 160))))))) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [eAC, e' ((2 * (10 ^ 40 + 1)) ^ (c - 160))]
      simp only [Nat.mul_assoc]
    have eR : ((Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap)) *
        (m * 9999999999999999999999999996615 * (10 ^ 40 : Nat) ^ (c - 160))) *
        (10 ^ 18 * (10 ^ 31 - 10)) =
        x * Sc * (2 ^ (c - 160) * (10 ^ 40 : Nat) ^ (c - 160) * (10 ^ 31 - 3385) *
          (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap) *
          (10 ^ 31 - 10) * 10 ^ 18) := by
      rw [hmx, show (9999999999999999999999999996615 : Nat) = 10 ^ 31 - 3385 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    unfold wadRayNum wadRayStrictDen
    generalize hT1 : x * 10 ^ 31 * (((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
      (560227709747861399187319382270000000000000000000000000000000 *
        (2 * (10 ^ 40 + 1)) ^ (c - 160))) = T1 at eL ⊢
    generalize hT2 : x * Sc * ((10 : Nat) ^ 142 * (2 * (10 ^ 40 + 1)) ^ (c - 160)) = T2
      at eL hbf
    generalize hT3 : x * Sc * (2 ^ (c - 160) * (10 ^ 40 : Nat) ^ (c - 160) *
      (10 ^ 31 - 3385) * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap) *
      (10 ^ 31 - 10) * 10 ^ 18) = T3 at eR hbf
    generalize hT4 : ((Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap)) *
      (m * 9999999999999999999999999996615 * (10 ^ 40 : Nat) ^ (c - 160))) *
      (10 ^ 18 * (10 ^ 31 - 10)) = T4 at eR ⊢
    omega

end LnFloorCert
