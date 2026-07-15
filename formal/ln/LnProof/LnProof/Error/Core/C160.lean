import LnProof.Floor.CutEquiv
import LnProof.Error.Cert
import LnProof.Error.Core.CutDefs
import LnProof.Error.Core.Args

/-!
# Error bound — C160

Negative-argument lemmas and the `lo_*_c160_exact` brackets.
-/

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

namespace LnFloorCert

open LnYul LnFloor Common.Exp Common.Poly

attribute [local irreducible] lnWadToRayBody

theorem ln_err_arg_nonneg {r : Int} (hr0 : -1 ≤ r) :
    0 ≤ r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int) := by
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

theorem ln_err_neg_arg_nonneg {r : Int} (hr : r ≤ -2) :
    0 ≤ -(r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) := by
  unfold lnErrorBoundDen lnErrorBoundNum
  omega

theorem ln_err_neg_arg_le_int {A r : Int}
    (hA : A ≤ (r + 1) * twoPow99I - twoPow27I) (_hr : r ≤ -2) :
    (-(r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int))) * twoPow99I ≤
      -(A * (lnErrorBoundDen : Int) + 698600000 * twoPow99I) := by
  unfold twoPow99I twoPow27I at hA
  have hmul := Int.mul_le_mul_of_nonneg_right hA (by decide : 0 ≤ (1000000000 : Int))
  have eDen : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
    unfold lnErrorBoundDen
    rfl
  have eNum : ((lnErrorBoundNum : Nat) : Int) = (1698600000 : Int) := by
    unfold lnErrorBoundNum
    rfl
  rw [eDen, eNum]
  unfold twoPow99I
  omega

theorem v_c160_nonneg {m : Nat} (h1 : MLO ≤ m) (h2 : m < MHI) :
    0 ≤ int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt 160 +
      lnBiasI := by
  have hb := (LnYul.r1_bound h1 h2).1
  have hm := Int.mul_le_mul_of_nonneg_right hb
    (by decide : 0 ≤ (7450580596923828125 : Int))
  have hfloor :
      0 ≤
        (-(240000000000000000000000000000 : Int)) *
          7450580596923828125 + lnBiasI := by
    unfold lnBiasI
    decide
  have hln2 : ln2kInt 160 = 0 := by
    unfold ln2kInt
    rw [if_pos (by decide)]
    decide
  rw [hln2]
  omega

theorem lo_ge_c160_exact {m x : Nat} {r : Int} (h1 : Sc ≤ m) (h2 : m < MHI)
    (hr : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt 160 +
      116873961749927929127912020551560854268589826112230 < (r + 1) * 2 ^ 72)
    (hr0 : -1 ≤ r) (hmx : m ≤ x) (hxm : x < m + 1) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have hx : x = m := by omega
  subst x
  have hX1 := x1_nonneg_geF h1 h2
  have harg_nonneg := ln_err_arg_nonneg hr0
  have cap1 := capLB_lift_right (den := lnErrorBoundDen) QS_pos (x1capGeLoF h1 h2)
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos capBL
  have cap12 := capLB_mul cap1 capB
  have cap123 := capLB_mul cap12 capEFracL
  have hmul :
      ((int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 *
        lnErrorBoundDen + BIASc * 2 ^ 27 * lnErrorBoundDen +
          lnErrorExtraNum * 2 ^ 99) * lnErrQ ≤ lnErrArg r * lnErrQ := by
    have hmul0 :
        ((((int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 +
          BIASc * 2 ^ 27) * lnErrorBoundDen +
            lnErrorExtraNum * 2 ^ 99) * lnErrQ ≤ lnErrArg r * lnErrQ) := by
      simpa [lnErrArg, lnErrQ] using
      Nat.mul_le_mul_right (QS * lnErrorBoundDen)
        (c160_phase_arg_le (X := int256 (x1W (zWord m))) hX1
          (phase_lt_scaled_le hr) harg_nonneg)
    have hdist :
        (int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 *
          lnErrorBoundDen + BIASc * 2 ^ 27 * lnErrorBoundDen +
            lnErrorExtraNum * 2 ^ 99 =
        (((int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 +
          BIASc * 2 ^ 27) * lnErrorBoundDen +
            lnErrorExtraNum * 2 ^ 99) := by
      rw [Nat.add_mul]
    rw [hdist]
    exact hmul0
  have capR : capLB (lnErrArg r) lnErrQ
      (((m * 9999999999999999999999999996615) * (Sc * (10 ^ 31 - 3384))) *
        (10 ^ 31 + lnErrorExtraCap))
      ((560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) :=
    @capLB_arg
      (lnErrArg r) lnErrQ
      (((int256 (x1W (zWord m))).toNat * 1000000000000000000000000000 *
        lnErrorBoundDen + BIASc * 2 ^ 27 * lnErrorBoundDen +
          lnErrorExtraNum * 2 ^ 99))
      lnErrQ
      ((((m * 9999999999999999999999999996615) * (Sc * (10 ^ 31 - 3384))) *
        (10 ^ 31 + lnErrorExtraCap)))
      (((560227709747861399187319382270000000000000000000000000000000 *
        (10 ^ 18 * 10 ^ 31)) * 10 ^ 31))
      (by unfold lnErrQ; decide) hmul cap123
  refine capLB_weaken (p := lnErrArg r) (q := lnErrQ)
    (y := ((m * 9999999999999999999999999996615) * (Sc * (10 ^ 31 - 3384))) *
      (10 ^ 31 + lnErrorExtraCap))
    (w := ((560227709747861399187319382270000000000000000000000000000000 *
      (10 ^ 18 * 10 ^ 31)) * 10 ^ 31))
    ?_ capR ?_
  · have h1' : 0 < (560227709747861399187319382270000000000000000000000000000000 : Nat) *
        (10 ^ 18 * 10 ^ 31) := by decide
    exact Nat.mul_pos h1' (by decide)
  · have hb := Nat.mul_le_mul_left (m * Sc) errBudgetL0_exact
    have eL : (m * 10 ^ 31) *
        ((560227709747861399187319382270000000000000000000000000000000 *
          (10 ^ 18 * 10 ^ 31)) * 10 ^ 31) =
        m * Sc * (10 : Nat) ^ 142 := by
      rw [show (560227709747861399187319382270000000000000000000000000000000 : Nat) =
        Sc * (10 : Nat) ^ 31 from by unfold Sc; decide]
      ring_nf
    have eR : (((m * 9999999999999999999999999996615) *
          (Sc * (10 ^ 31 - 3384))) * (10 ^ 31 + lnErrorExtraCap)) *
          (10 ^ 18 * (10 ^ 31 - 10)) =
        m * Sc * (((10 : Nat) ^ 31 - 3385) * ((10 : Nat) ^ 31 - 3384) *
          ((10 : Nat) ^ 31 + lnErrorExtraCap) * ((10 : Nat) ^ 31 - 10) *
            (10 : Nat) ^ 18) := by
      rw [show (9999999999999999999999999996615 : Nat) = (10 : Nat) ^ 31 - 3385
        from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    unfold wadRayNum wadRayStrictDen
    rw [eL, eR]
    exact hb

theorem lo_lt_c160_exact {m x : Nat} {r : Int} (h1 : MLO ≤ m) (h2 : m < Sc)
    (hr : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt 160 +
      116873961749927929127912020551560854268589826112230 < (r + 1) * 2 ^ 72)
    (hmx : m ≤ x) (hxm : x < m + 1) :
    capLB (lnErrArg r) lnErrQ (wadRayNum x) wadRayStrictDen := by
  have hx : x = m := by omega
  subst x
  have hmhi : m < MHI := by
    simp only [Sc, MHI] at h2 ⊢
    omega
  have hV0I := v_c160_nonneg h1 hmhi
  have hV0 : 0 ≤ int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt 160 +
      116873961749927929127912020551560854268589826112230 := by
    simpa [lnBiasI] using hV0I
  have hr0 : -1 ≤ r := by
    rcases Int.lt_or_le r (-1) with hlt | hle
    · exfalso
      have hrle : (r + 1) * 2 ^ 72 ≤ 0 := by
        have hle' : r + 1 ≤ 0 := by omega
        exact Int.mul_le_mul_of_nonneg_right hle' (by decide : (0 : Int) ≤ 2 ^ 72)
      omega
    · exact hle
  have hX1 := x1_nonpos_ltF h1 h2
  have harg_nonneg := ln_err_arg_nonneg hr0
  have cap1 := capUB_lift_right (den := lnErrorBoundDen) QS_pos (x1capLtLoF h1 h2)
  have capB := capLB_lift_right (den := lnErrorBoundDen) QS_pos capBL
  have capBE := capLB_mul capB capEFracL
  change capUB ((-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen)
    lnErrQ 560227709747861399187319382270000000000000000000000000000000
      (m * 9999999999999999999999999996615) at cap1
  change capLB (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N)
    lnErrQ (Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorExtraCap))
      (10 ^ 18 * 10 ^ 31 * 10 ^ 31) at capBE
  have hVs0 : (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt 160 +
        lnBiasI) * twoPow27I =
      int256 (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I := by
    have hVs := v_scale_pos (int256 (x1W (zWord m))) 160 (by decide)
    simpa only [Nat.sub_self, Nat.zero_mul, Int.natCast_zero, Int.zero_mul,
      Int.add_zero, twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
  have hV0s : 0 ≤
      int256 (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I := by
    have hpow27 : (0 : Int) ≤ twoPow27I := by
      unfold twoPow27I
      decide
    have h := Int.mul_le_mul_of_nonneg_right hV0I hpow27
    rw [hVs0] at h
    exact h
  have hnegXn :
      (((-int256 (x1W (zWord m))).toNat : Nat) : Int) =
        -int256 (x1W (zWord m)) :=
    Int.toNat_of_nonneg (by omega)
  have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
    unfold twoPow27N twoPow27I lnBiasI
    decide +kernel
  have hscale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := rfl
  have hden : ((lnErrorBoundDen : Nat) : Int) = (1000000000 : Int) := by
    unfold lnErrorBoundDen
    rfl
  have hextra : ((lnErrorExtraNum * twoPow99N : Nat) : Int) =
      698600000 * twoPow99I := by
    unfold lnErrorExtraNum lnErrorBoundNum lnErrorBoundDen twoPow99N twoPow99I
    decide +kernel
  have hsub_le : (-int256 (x1W (zWord m))).toNat * lnPhaseScaleN *
        lnErrorBoundDen ≤
      BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N := by
    apply Int.ofNat_le.mp
    simp only [Int.natCast_add, Int.natCast_mul, hnegXn, hBc, hscale, hden, hextra]
    have hmain : (-int256 (x1W (zWord m))) * lnPhaseScaleI ≤ lnBiasI * twoPow27I := by
      rw [Int.neg_mul]
      generalize int256 (x1W (zWord m)) * lnPhaseScaleI = A at hV0s ⊢
      generalize lnBiasI * twoPow27I = B at hV0s ⊢
      omega
    have hmul := Int.mul_le_mul_of_nonneg_right hmain (by decide : 0 ≤ (1000000000 : Int))
    have hnon : 0 ≤ 698600000 * twoPow99I := by
      unfold twoPow99I
      decide
    exact Int.le_trans hmul (Int.le_add_of_nonneg_right hnon)
  have hsplit :
      BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N =
        (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
          (-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen) +
          (-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen := by
    exact (Nat.sub_add_cancel hsub_le).symm
  rw [hsplit] at capBE
  have capV := capLB_cancel (q := lnErrQ) (by unfold lnErrQ; decide) capBE cap1
  have hple :
      BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
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
        (((BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
          (-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen : Nat) : Int)) =
        (int256 (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I) *
            (1000000000 : Int) + 698600000 * twoPow99I := by
      have hsI := congrArg (fun n : Nat => ((n : Nat) : Int)) hsplit
      simp only [Int.natCast_add, Int.natCast_mul, hnegXn, hBc, hscale, hden, hextra] at hsI
      rw [Int.neg_mul] at hsI
      generalize (((BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
        (-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen : Nat) : Int)) = S
        at hsI ⊢
      generalize int256 (x1W (zWord m)) * lnPhaseScaleI = A at hsI ⊢
      generalize lnBiasI * twoPow27I = B at hsI ⊢
      generalize 698600000 * twoPow99I = E at hsI ⊢
      omega
    rw [lnErrArg, htarget, hsub_cast]
    have hsc : (int256 (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I) ≤
        (r + 1) * twoPow99I - twoPow27I := by
      have hrI : int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt 160 +
          lnBiasI < (r + 1) * 2 ^ 72 := by
        simpa [lnBiasI] using hr
      have h := phase_lt_scaled_le hrI
      change (int256 (x1W (zWord m)) * 7450580596923828125 + ln2kInt 160 +
          lnBiasI) * twoPow27I ≤ ((r + 1) * twoPow72I - 1) * twoPow27I at h
      rw [hVs0] at h
      have er : ((r + 1) * twoPow72I - 1) * twoPow27I =
          (r + 1) * twoPow99I - twoPow27I := by
        unfold twoPow72I twoPow27I twoPow99I
        rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
          by decide]
        omega
      rw [er] at h
      exact h
    have hcore := c160_arg_le_int (A :=
        int256 (x1W (zWord m)) * lnPhaseScaleI + lnBiasI * twoPow27I) (r := r) hsc
    simpa [lnErrorBoundDen, lnErrorBoundNum, twoPow99I] using hcore
  have hmul :
      (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
          (-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen) * lnErrQ ≤
        lnErrArg r * lnErrQ :=
    Nat.mul_le_mul_right _ hple
  have capR : capLB (lnErrArg r) lnErrQ
      ((Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorExtraCap)) *
        (m * 9999999999999999999999999996615))
      (((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
        560227709747861399187319382270000000000000000000000000000000) :=
    @capLB_arg
      (lnErrArg r) lnErrQ
      (BIASc * twoPow27N * lnErrorBoundDen + lnErrorExtraNum * twoPow99N -
        (-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen)
      lnErrQ
      ((Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorExtraCap)) *
        (m * 9999999999999999999999999996615))
      (((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
        560227709747861399187319382270000000000000000000000000000000)
      (by unfold lnErrQ; decide) hmul capV
  refine capLB_weaken (p := lnErrArg r) (q := lnErrQ)
    (y := (Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorExtraCap)) *
      (m * 9999999999999999999999999996615))
    (w := ((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
      560227709747861399187319382270000000000000000000000000000000)
    ?_ capR ?_
  · have h1' : 0 < ((10 ^ 18 * 10 ^ 31) * 10 ^ 31 : Nat) := by decide
    exact Nat.mul_pos h1' (by decide)
  · have hb := Nat.mul_le_mul_left (m * Sc) errBudgetL0_exact
    have eL : (m * 10 ^ 31) *
        (((10 ^ 18 * 10 ^ 31) * 10 ^ 31) *
          560227709747861399187319382270000000000000000000000000000000) =
        m * Sc * (10 : Nat) ^ 142 := by
      rw [show (560227709747861399187319382270000000000000000000000000000000 : Nat) =
        Sc * (10 : Nat) ^ 31 from by unfold Sc; decide]
      ring_nf
    have eR : ((Sc * (10 ^ 31 - 3384) * (10 ^ 31 + lnErrorExtraCap)) *
          (m * 9999999999999999999999999996615)) *
          (10 ^ 18 * (10 ^ 31 - 10)) =
        m * Sc * (((10 : Nat) ^ 31 - 3385) * ((10 : Nat) ^ 31 - 3384) *
          ((10 : Nat) ^ 31 + lnErrorExtraCap) * ((10 : Nat) ^ 31 - 10) *
            (10 : Nat) ^ 18) := by
      rw [show (9999999999999999999999999996615 : Nat) = (10 : Nat) ^ 31 - 3385
        from by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    unfold wadRayNum wadRayStrictDen
    rw [eL, eR]
    exact hb

end LnFloorCert
