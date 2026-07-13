import LnProof.Floor.CutEquiv
import LnProof.Error.Cert
import LnProof.Error.Core.CutDefs
import LnProof.Error.Core.C160

/-!
# Error bound — BranchBn

Below-`n` exact brackets: `bn_ge_neg_exact`, `bn_lt_neg_exact`.
-/

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

namespace LnFloorCert

open LnYul LnFloor Common.Exp Common.Poly

attribute [local irreducible] lnWadToRayBody


theorem bn_ge_neg_exact {m c x : Nat} {r : Int} (h1 : Sc ≤ m) (h2 : m < MHI)
    (hc : 160 < c) (hc2 : c ≤ 255)
    (hr : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551516294209054209107914 < (r + 1) * 2 ^ 72)
    (hrneg : r ≤ -2)
    (hmx : m = x * 2 ^ (c - 160)) :
    capUB (lnErrNegArg r) lnErrQ wadRayStrictDen (wadRayNum x) := by
  have hneg_nonneg := ln_err_neg_arg_nonneg hrneg
  have cap1 := capLB_lift_right (den := lnErrorBoundDen) QS_pos (x1capGeLoF h1 h2)
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos capBL
  have cap1B := capLB_mul cap1 capB
  have hb := capLB_mul cap1B capECoarseNegL
  have cap2UQ := capUB_lift_right (den := lnErrorBoundDen) QS_pos cap2U
  have hsum := capUB_pow (by unfold QS lnErrorBoundDen; decide) cap2UQ (c - 160)
  have hX1 := x1_nonneg_geF h1 h2
  have hVs := v_scale_neg (int256 (x1W (zWord m))) c hc
  have hgap : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551516294209054209107914) * 2 ^ 27 ≤
      (r + 1) * 2 ^ 99 - 2 ^ 27 := by
    have hsc := Int.mul_le_mul_of_nonneg_right
      (show int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551516294209054209107914 ≤ (r + 1) * 2 ^ 72 - 1
        from by omega) (by decide : (0 : Int) ≤ 2 ^ 27)
    have er : ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 = (r + 1) * 2 ^ 99 - 2 ^ 27 := by
      rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
        by decide]
      omega
    rw [er] at hsc
    exact hsc
  change capLB ((int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
      BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N)
    lnErrQ
      ((m * 9999999999999999999999999996615) * (Sc * (10 ^ 31 - 3384)) *
        (10 ^ 31 + lnErrorCoarseNegBudgetCap))
      ((560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) at hb
  have hcancel_le :
      (int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N ≤
        (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) := by
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
    have hVsI :
        (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
            lnBiasI) * twoPow27I +
          ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) =
        int256 (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I := by
      simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
    have hgapI : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        lnBiasI) * twoPow27I ≤ (r + 1) * twoPow99I - twoPow27I := by
      simpa [lnBiasI, twoPow27I, twoPow99I] using hgap
    generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI) * twoPow27I = V27 at hgapI hVsI
    generalize hgA : int256 (x1W (zWord m)) * lnPhaseScaleI = A at hVsI
    generalize hgB : ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = B at hgapI hVsI hLc
    generalize hgC : (c - 160) * (LN2c * twoPow27N) = Cn at hLc ⊢
    generalize hgD : (int256 (x1W (zWord m))).toNat * lnPhaseScaleN = D at ⊢
    have hAD : (D : Int) = A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n, hscale]
    generalize hgE : BIASc * twoPow27N = E at hBc ⊢
    generalize hgBias : lnBiasI * twoPow27I = Bias at hVsI hBc
    generalize hgX : lnErrorExtraNum * twoPow99N = Ex at hextra ⊢
    have hN : (((c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
        B * (1000000000 : Int) := by
      rw [show (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
          Cn * lnErrorBoundDen by
            rw [← hgC]
            simp only [Nat.mul_assoc]]
      simp only [Int.natCast_mul, hLc, hden]
    clear hX1n hX1 cap1 capB cap1B hb cap2UQ hsum hr h1 h2 hc hc2 hmx hVs
    simp only [Int.natCast_add, Int.natCast_mul, hden, hAD, hBc, hextra, hN]
    unfold twoPow99I twoPow27I at hgapI
    unfold twoPow99I at ⊢
    omega
  have hsplit : (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
      ((c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) -
        ((int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N)) +
        ((int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N) := by
    exact (Nat.sub_add_cancel hcancel_le).symm
  change capUB ((c - 160) * (LN2c * twoPow27N * lnErrorBoundDen)) lnErrQ
    ((2 * (10 ^ 40 + 1)) ^ (c - 160)) ((10 ^ 40) ^ (c - 160)) at hsum
  rw [hsplit] at hsum
  have capV := capUB_cancel (q := lnErrQ) (by unfold lnErrQ; decide) hsum hb
  have hple : lnErrNegArg r ≤
      (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) -
        ((int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N) := by
    apply Int.ofNat_le.mp
    have htarget : (((-(r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int))).toNat *
        2 ^ 99 : Nat) : Int) =
        (-(r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int))) * twoPow99I := by
      rw [Int.natCast_mul, Int.toNat_of_nonneg hneg_nonneg]
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
    have hN : (((c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) : Nat) : Int) =
        (((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I)) *
          (1000000000 : Int) := by
      rw [show (c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) =
          ((c - 160) * (LN2c * twoPow27N)) * lnErrorBoundDen by
            simp only [Nat.mul_assoc]]
      simp only [Int.natCast_mul, hLc, hden]
    have hsub_cast :
        ((((c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) -
          ((int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
            BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N) : Nat) : Int)) =
        -((int256 (x1W (zWord m)) * lnPhaseScaleI -
            ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
            lnBiasI * twoPow27I) * (1000000000 : Int) +
          698600000 * twoPow99I) := by
      have hsI := congrArg (fun n : Nat => ((n : Nat) : Int)) hsplit
      simp only [Int.natCast_add, Int.natCast_mul, hX1n, hBc, hN, hden,
        hextra, hscale] at hsI
      generalize ((((c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) -
          ((int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
            BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N) : Nat) : Int)) = S
        at hsI ⊢
      generalize int256 (x1W (zWord m)) * lnPhaseScaleI = A at hsI ⊢
      generalize ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = B at hsI ⊢
      generalize lnBiasI * twoPow27I = C at hsI ⊢
      generalize 698600000 * twoPow99I = E at hsI ⊢
      omega
    rw [lnErrNegArg, htarget, hsub_cast]
    have hsc : int256 (x1W (zWord m)) * lnPhaseScaleI -
          ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
          lnBiasI * twoPow27I ≤
        (r + 1) * twoPow99I - twoPow27I := by
      have hVsI :
          (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
              lnBiasI) * twoPow27I +
            ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) =
          int256 (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I := by
        simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
      have hgapI : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
          lnBiasI) * twoPow27I ≤ (r + 1) * twoPow99I - twoPow27I := by
        simpa [lnBiasI, twoPow27I, twoPow99I] using hgap
      generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 +
        ln2kInt c + lnBiasI) * twoPow27I = V27 at hgapI hVsI
      generalize hgL : ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = L at hVsI ⊢
      generalize hgA : int256 (x1W (zWord m)) * lnPhaseScaleI = A at hVsI ⊢
      generalize hgB : lnBiasI * twoPow27I = B at hVsI ⊢
      omega
    exact ln_err_neg_arg_le_int hsc hrneg
  have hmul : lnErrNegArg r * lnErrQ ≤
      ((c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) -
        ((int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N)) * lnErrQ :=
    Nat.mul_le_mul_right _ hple
  have capR0 : capUB (lnErrNegArg r) lnErrQ
      ((2 * (10 ^ 40 + 1)) ^ (c - 160) *
        (560227709747861399187319382270000000000000000000000000000000 *
          (10 ^ 18 * 10 ^ 31) * 10 ^ 31))
      ((10 ^ 40) ^ (c - 160) *
        (m * 9999999999999999999999999996615 * (Sc * (10 ^ 31 - 3384)) *
          (10 ^ 31 + lnErrorCoarseNegBudgetCap))) :=
    @capUB_arg
      (lnErrNegArg r) lnErrQ
      ((c - 160) * ((LN2c * twoPow27N) * lnErrorBoundDen) -
        ((int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N))
      lnErrQ
      ((2 * (10 ^ 40 + 1)) ^ (c - 160) *
        (560227709747861399187319382270000000000000000000000000000000 *
          (10 ^ 18 * 10 ^ 31) * 10 ^ 31))
      ((10 ^ 40) ^ (c - 160) *
        (m * 9999999999999999999999999996615 * (Sc * (10 ^ 31 - 3384)) *
          (10 ^ 31 + lnErrorCoarseNegBudgetCap)))
      (by unfold lnErrQ; decide) hmul capV
  refine capUB_weaken (p := lnErrNegArg r) (q := lnErrQ)
    (y := ((2 * (10 ^ 40 + 1)) ^ (c - 160) *
      (560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 31) * 10 ^ 31)))
    (w := ((10 ^ 40) ^ (c - 160) *
      (m * 9999999999999999999999999996615 * (Sc * (10 ^ 31 - 3384)) *
        (10 ^ 31 + lnErrorCoarseNegBudgetCap)))) ?_ capR0 ?_
  · have h1' : 0 < (10 ^ 40 : Nat) ^ (c - 160) := Nat.pow_pos (by decide)
    have hm0 : 0 < m := by simp only [Sc] at h1; omega
    have hScp : 0 < Sc := by simp only [Sc]; omega
    exact Nat.mul_pos h1'
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hm0 (by decide))
        (Nat.mul_pos hScp (by decide))) (by decide))
  · have hbg := errBudgetBn_le (j := c - 160) (by omega)
    have hbf := Nat.mul_le_mul_left (x * Sc) hbg
    have eL : ((2 * (10 ^ 40 + 1)) ^ (c - 160) *
        (560227709747861399187319382270000000000000000000000000000000 *
          (10 ^ 18 * 10 ^ 31) * 10 ^ 31)) * (x * 10 ^ 31) =
        x * Sc * ((2 * (10 ^ 40 + 1)) ^ (c - 160) * (10 : Nat) ^ 31 *
          (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * 10 ^ 31) := by
      rw [show (560227709747861399187319382270000000000000000000000000000000 : Nat) =
        Sc * 10 ^ 31 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have eR : (10 ^ 18 * (10 ^ 31 - 10)) *
        ((10 ^ 40 : Nat) ^ (c - 160) *
          (m * 9999999999999999999999999996615 * (Sc * (10 ^ 31 - 3384)) *
            (10 ^ 31 + lnErrorCoarseNegBudgetCap))) =
        x * Sc * (10 ^ 18 * (10 ^ 31 - 10) * (10 ^ 40 : Nat) ^ (c - 160) *
          2 ^ (c - 160) * (10 ^ 31 - 3385) * (10 ^ 31 - 3384) *
          (10 ^ 31 + lnErrorCoarseNegBudgetCap)) := by
      rw [hmx, show (9999999999999999999999999996615 : Nat) = 10 ^ 31 - 3385 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    unfold wadRayNum wadRayStrictDen
    generalize hT1 : ((2 * (10 ^ 40 + 1)) ^ (c - 160) *
      (560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 31) * 10 ^ 31)) * (x * 10 ^ 31) = T1 at eL ⊢
    generalize hT2 : x * Sc * ((2 * (10 ^ 40 + 1)) ^ (c - 160) * (10 : Nat) ^ 31 *
      (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * 10 ^ 31) = T2 at eL hbf
    generalize hT3 : x * Sc * (10 ^ 18 * (10 ^ 31 - 10) * (10 ^ 40 : Nat) ^ (c - 160) *
      2 ^ (c - 160) * (10 ^ 31 - 3385) * (10 ^ 31 - 3384) *
      (10 ^ 31 + lnErrorCoarseNegBudgetCap)) = T3 at eR hbf
    generalize hT4 : (10 ^ 18 * (10 ^ 31 - 10)) *
      ((10 ^ 40 : Nat) ^ (c - 160) *
        (m * 9999999999999999999999999996615 * (Sc * (10 ^ 31 - 3384)) *
          (10 ^ 31 + lnErrorCoarseNegBudgetCap))) = T4 at eR ⊢
    omega

theorem bn_lt_neg_exact {m c x : Nat} {r : Int} (h1 : MLO ≤ m) (h2 : m < Sc)
    (hc : 160 < c) (hc2 : c ≤ 255)
    (hr : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551516294209054209107914 < (r + 1) * 2 ^ 72)
    (hrneg : r ≤ -2)
    (hmx : m = x * 2 ^ (c - 160)) :
    capUB (lnErrNegArg r) lnErrQ wadRayStrictDen (wadRayNum x) := by
  have hneg_nonneg := ln_err_neg_arg_nonneg hrneg
  have cap1 := capUB_lift_right (den := lnErrorBoundDen) QS_pos (x1capLtLoF h1 h2)
  have cap2UQ := capUB_lift_right (den := lnErrorBoundDen) QS_pos cap2U
  have hsum := capUB_mul (by unfold QS lnErrorBoundDen; decide) cap1
    (capUB_pow (by unfold QS lnErrorBoundDen; decide) cap2UQ (c - 160))
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos capBL
  have hb := capLB_mul capB capECoarseNegL
  have hX1 := x1_nonpos_ltF h1 h2
  have hVs := v_scale_neg (int256 (x1W (zWord m))) c hc
  have hgap : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      116873961749927929127912020551516294209054209107914) * 2 ^ 27 ≤
      (r + 1) * 2 ^ 99 - 2 ^ 27 := by
    have hsc := Int.mul_le_mul_of_nonneg_right
      (show int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        116873961749927929127912020551516294209054209107914 ≤ (r + 1) * 2 ^ 72 - 1
        from by omega) (by decide : (0 : Int) ≤ 2 ^ 27)
    have er : ((r + 1) * 2 ^ 72 - 1) * 2 ^ 27 = (r + 1) * 2 ^ 99 - 2 ^ 27 := by
      rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
        by decide]
      omega
    rw [er] at hsc
    exact hsc
  change capUB ((-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
      (c - 160) * (LN2c * twoPow27N * lnErrorBoundDen))
    lnErrQ
      (560227709747861399187319382270000000000000000000000000000000 *
        ((2 * (10 ^ 40 + 1)) ^ (c - 160)))
      ((m * 9999999999999999999999999996615) * ((10 ^ 40) ^ (c - 160))) at hsum
  change capLB (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N)
    lnErrQ (Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap))
      ((10 ^ 18 * 10 ^ 31) * 10 ^ 31) at hb
  have hcancel_le : BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N ≤
      (-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        (c - 160) * (LN2c * twoPow27N * lnErrorBoundDen) := by
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
    have hVsI :
        (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
            lnBiasI) * twoPow27I +
          ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) =
        int256 (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I := by
      simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
    have hgapI : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
        lnBiasI) * twoPow27I ≤ (r + 1) * twoPow99I - twoPow27I := by
      simpa [lnBiasI, twoPow27I, twoPow99I] using hgap
    generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
      lnBiasI) * twoPow27I = V27 at hgapI hVsI
    generalize hgA : int256 (x1W (zWord m)) * lnPhaseScaleI = A at hVsI
    generalize hgB : ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = B at hgapI hVsI hLc
    generalize hgC : (c - 160) * (LN2c * twoPow27N) = Cn at hLc ⊢
    generalize hgD : (-int256 (x1W (zWord m))).toNat * lnPhaseScaleN = D at ⊢
    have hAD : (D : Int) = -A := by
      rw [← hgA, ← hgD, Int.natCast_mul, hX1n, hscale]
      rw [Int.neg_mul]
    generalize hgE : BIASc * twoPow27N = E at hBc ⊢
    generalize hgBias : lnBiasI * twoPow27I = Bias at hVsI hBc
    generalize hgX : lnErrorExtraNum * twoPow99N = Ex at hextra ⊢
    have hN : (((c - 160) * (LN2c * twoPow27N * lnErrorBoundDen) : Nat) : Int) =
        B * (1000000000 : Int) := by
      rw [show (c - 160) * (LN2c * twoPow27N * lnErrorBoundDen) =
          Cn * lnErrorBoundDen by
            rw [← hgC]
            simp only [Nat.mul_assoc]]
      simp only [Int.natCast_mul, hLc, hden]
    clear hX1n hX1 cap1 cap2UQ hsum capB hb hr h1 h2 hc hc2 hmx hVs
    simp only [Int.natCast_add, Int.natCast_mul, hden, hAD, hBc, hextra, hN]
    unfold twoPow99I twoPow27I at hgapI
    unfold twoPow99I at ⊢
    omega
  have hsplit : (-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
      (c - 160) * (LN2c * twoPow27N * lnErrorBoundDen) =
      ((-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        (c - 160) * (LN2c * twoPow27N * lnErrorBoundDen) -
          (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N)) +
        (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N) := by
    exact (Nat.sub_add_cancel hcancel_le).symm
  rw [hsplit] at hsum
  have capV := capUB_cancel (q := lnErrQ) (by unfold lnErrQ; decide) hsum hb
  have hple : lnErrNegArg r ≤
      (-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        (c - 160) * (LN2c * twoPow27N * lnErrorBoundDen) -
          (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N) := by
    apply Int.ofNat_le.mp
    have htarget : (((-(r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int))).toNat *
        2 ^ 99 : Nat) : Int) =
        (-(r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int))) * twoPow99I := by
      rw [Int.natCast_mul, Int.toNat_of_nonneg hneg_nonneg]
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
    have hN : (((c - 160) * (LN2c * twoPow27N * lnErrorBoundDen) : Nat) : Int) =
        (((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I)) *
          (1000000000 : Int) := by
      rw [show (c - 160) * (LN2c * twoPow27N * lnErrorBoundDen) =
          ((c - 160) * (LN2c * twoPow27N)) * lnErrorBoundDen by
            simp only [Nat.mul_assoc]]
      simp only [Int.natCast_mul, hLc, hden]
    have hsub_cast :
        ((((-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
          (c - 160) * (LN2c * twoPow27N * lnErrorBoundDen) -
          (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N) : Nat) : Int)) =
        -((int256 (x1W (zWord m)) * lnPhaseScaleI -
            ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
            lnBiasI * twoPow27I) * (1000000000 : Int) +
          698600000 * twoPow99I) := by
      have hsI := congrArg (fun n : Nat => ((n : Nat) : Int)) hsplit
      simp only [Int.natCast_add, Int.natCast_mul, hX1n, hBc, hN, hden,
        hextra, hscale] at hsI
      rw [show -int256 (x1W (zWord m)) * lnPhaseScaleI =
          -(int256 (x1W (zWord m)) * lnPhaseScaleI) by rw [Int.neg_mul]] at hsI
      generalize ((((-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        (c - 160) * (LN2c * twoPow27N * lnErrorBoundDen) -
        (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N) : Nat) : Int)) = S
        at hsI ⊢
      generalize int256 (x1W (zWord m)) * lnPhaseScaleI = A at hsI ⊢
      generalize ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = B at hsI ⊢
      generalize lnBiasI * twoPow27I = C at hsI ⊢
      generalize 698600000 * twoPow99I = E at hsI ⊢
      omega
    rw [lnErrNegArg, htarget, hsub_cast]
    have hsc : int256 (x1W (zWord m)) * lnPhaseScaleI -
          ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) +
          lnBiasI * twoPow27I ≤
        (r + 1) * twoPow99I - twoPow27I := by
      have hVsI :
          (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
              lnBiasI) * twoPow27I +
            ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) =
          int256 (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I := by
        simpa [twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
      have hgapI : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt c +
          lnBiasI) * twoPow27I ≤ (r + 1) * twoPow99I - twoPow27I := by
        simpa [lnBiasI, twoPow27I, twoPow99I] using hgap
      generalize hgV : (int256 (x1W (zWord m)) * 7450580596923828125 +
        ln2kInt c + lnBiasI) * twoPow27I = V27 at hgapI hVsI
      generalize hgL : ((c - 160 : Nat) : Int) * ((LN2c : Int) * twoPow27I) = L at hVsI ⊢
      generalize hgA : int256 (x1W (zWord m)) * lnPhaseScaleI = A at hVsI ⊢
      generalize hgB : lnBiasI * twoPow27I = B at hVsI ⊢
      omega
    exact ln_err_neg_arg_le_int hsc hrneg
  have hmul : lnErrNegArg r * lnErrQ ≤
      ((-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
        (c - 160) * (LN2c * twoPow27N * lnErrorBoundDen) -
          (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N)) * lnErrQ :=
    Nat.mul_le_mul_right _ hple
  have capR0 := capUB_arg (q := lnErrQ) (by unfold lnErrQ; decide) hmul capV
  refine capUB_weaken ?_ capR0 ?_
  · have hm0 : 0 < m := by simp only [MLO] at h1; omega
    have hScp : 0 < Sc := by simp only [Sc]; omega
    exact Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos hm0 (by omega)) (Nat.pow_pos (by omega)))
      (Nat.mul_pos (Nat.mul_pos hScp (by omega)) (by omega))
  · have hbg := errBudgetBn_le (j := c - 160) (by omega)
    have hbf := Nat.mul_le_mul_left (x * Sc) hbg
    have eL : 560227709747861399187319382270000000000000000000000000000000 *
        (2 * (10 ^ 40 + 1)) ^ (c - 160) * ((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
        (x * 10 ^ 31) =
        x * Sc * ((2 * (10 ^ 40 + 1)) ^ (c - 160) * (10 : Nat) ^ 31 *
          (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * 10 ^ 31) := by
      rw [show (560227709747861399187319382270000000000000000000000000000000 : Nat) =
        Sc * 10 ^ 31 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have eR : 10 ^ 18 * (10 ^ 31 - 10) * (m * 9999999999999999999999999996615 *
        (10 ^ 40 : Nat) ^ (c - 160) *
          (Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap))) =
        x * Sc * (10 ^ 18 * (10 ^ 31 - 10) * (10 ^ 40 : Nat) ^ (c - 160) *
          2 ^ (c - 160) * (10 ^ 31 - 3385) * (10 ^ 31 - 3384) *
          (10 ^ 31 + lnErrorCoarseNegBudgetCap)) := by
      rw [hmx, show (9999999999999999999999999996615 : Nat) = 10 ^ 31 - 3385 from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    unfold wadRayNum wadRayStrictDen
    generalize hT1 : 560227709747861399187319382270000000000000000000000000000000 *
      (2 * (10 ^ 40 + 1)) ^ (c - 160) * ((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
      (x * 10 ^ 31) = T1 at eL ⊢
    generalize hT2 : x * Sc * ((2 * (10 ^ 40 + 1)) ^ (c - 160) * (10 : Nat) ^ 31 *
      (10 ^ 18 * 10 ^ 31) * 10 ^ 31 * 10 ^ 31) = T2 at eL hbf
    generalize hT3 : x * Sc * (10 ^ 18 * (10 ^ 31 - 10) * (10 ^ 40 : Nat) ^ (c - 160) *
      2 ^ (c - 160) * (10 ^ 31 - 3385) * (10 ^ 31 - 3384) *
      (10 ^ 31 + lnErrorCoarseNegBudgetCap)) = T3 at eR hbf
    generalize hT4 : 10 ^ 18 * (10 ^ 31 - 10) * (m * 9999999999999999999999999996615 *
      (10 ^ 40 : Nat) ^ (c - 160) *
        (Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorCoarseNegBudgetCap))) = T4 at eR ⊢
    omega

end LnFloorCert
