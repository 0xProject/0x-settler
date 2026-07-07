import LnProof.Floor.CutEquiv
import LnProof.Error.Cert
import LnProof.Error.Core.CutDefs

/-!
# Error bound — Args

Cut at the special points (`x = 1`, `r = -1`) and the `c160` argument-bound lemmas.
-/

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

namespace LnFloorCert

open LnYul LnFloor Common.Exp Common.Poly

attribute [local irreducible] lnWadToRayBody


/-- The exact wad input has `r = 0`, and the published fractional bound is
large enough to clear the strictness denominator directly. -/
theorem cutLogWadRayLtRational_at_wad :
    CutLogWadRayLtRational (10 ^ 18) 0 lnErrorBoundNum lnErrorBoundDen := by
  apply CutLogWadRayLtRational_of_strict (by decide)
  unfold CutLogWadRayLtRationalStrict
  rw [if_pos]
  · change capLB (lnErrorBoundNum * 2 ^ 99) (QS * lnErrorBoundDen)
      (10 ^ 18 * 10 ^ 31) (10 ^ 18 * (10 ^ 31 - 10))
    refine ⟨1, ?_⟩
    simp only [fact, expNum, Nat.pow_one, Nat.mul_one]
    have h := Nat.mul_le_mul_right (2 ^ 99)
      (Nat.mul_le_mul_left (10 ^ 18) wad_exact_upper_budget)
    simpa [QS, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.left_distrib,
      Nat.right_distrib] using h
  · unfold lnErrorBoundNum lnErrorBoundDen
    decide

theorem cutLogWadRayLtRational_at_neg_one {x : Nat}
    (hx : x < 10 ^ 18) :
    CutLogWadRayLtRational x (-1) lnErrorBoundNum lnErrorBoundDen := by
  unfold CutLogWadRayLtRational
  rw [if_pos]
  · change capLB (((-1 : Int) * (lnErrorBoundDen : Int) +
        (lnErrorBoundNum : Int)).toNat * 2 ^ 99) (QS * lnErrorBoundDen)
      x (10 ^ 18)
    have hq : 0 < QS * lnErrorBoundDen := by
      unfold QS lnErrorBoundDen
      decide
    have cap0 : capLB 0 (QS * lnErrorBoundDen) 1 1 := capLB_one (QS * lnErrorBoundDen)
    have capA : capLB (((-1 : Int) * (lnErrorBoundDen : Int) +
        (lnErrorBoundNum : Int)).toNat * 2 ^ 99) (QS * lnErrorBoundDen) 1 1 := by
      refine capLB_arg hq ?_ cap0
      simp only [Nat.zero_mul, Nat.zero_le]
    refine capLB_weaken (p := (((-1 : Int) * (lnErrorBoundDen : Int) +
        (lnErrorBoundNum : Int)).toNat * 2 ^ 99)) (q := QS * lnErrorBoundDen)
        (y := 1) (w := 1) ?_ capA ?_
    · decide
    · simpa [Nat.mul_one, Nat.one_mul] using (by omega : x ≤ 10 ^ 18)
  · unfold lnErrorBoundNum lnErrorBoundDen
    decide

theorem c160_arg_le_int {A r : Int}
    (h : A ≤ (r + 1) * twoPow99I - twoPow27I) :
    A * 1000000000 + 698600000 * twoPow99I ≤
      (r * 1000000000 + 1698600000) * twoPow99I := by
  have hm : A * (1000000000 : Int) ≤
      ((r + 1) * twoPow99I - twoPow27I) * (1000000000 : Int) :=
    Int.mul_le_mul_of_nonneg_right h (by decide)
  have hle := Int.add_le_add_right hm (698600000 * twoPow99I)
  have e : ((r + 1) * twoPow99I - twoPow27I) *
        (1000000000 : Int) + 698600000 * twoPow99I =
      (r * 1000000000 + 1698600000) * twoPow99I -
        twoPow27I * (1000000000 : Int) := by
    simp only [Int.sub_mul, Int.add_mul, Int.one_mul]
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have hslack : 0 ≤ twoPow27I * (1000000000 : Int) :=
    Int.mul_nonneg (by unfold twoPow27I; decide) (by decide)
  calc
    A * 1000000000 + 698600000 * twoPow99I
        ≤ ((r + 1) * twoPow99I - twoPow27I) *
            1000000000 + 698600000 * twoPow99I := hle
    _ = (r * 1000000000 + 1698600000) * twoPow99I -
        twoPow27I * (1000000000 : Int) := e
    _ ≤ (r * 1000000000 + 1698600000) * twoPow99I :=
        Int.sub_le_self _ hslack

theorem c160_arg_le {a b : Nat} {r : Int}
    (h : (a : Int) + (b : Int) ≤ (r + 1) * twoPow99I - twoPow27I)
    (harg : 0 ≤ r * (1000000000 : Int) + 1698600000) :
    (a + b) * 1000000000 + 698600000 * twoPow99N ≤
      (r * (1000000000 : Int) + 1698600000).toNat * twoPow99N := by
  have hcast : (((r * (1000000000 : Int) + 1698600000).toNat : Nat) : Int) =
      r * (1000000000 : Int) + 1698600000 :=
    Int.toNat_of_nonneg harg
  have hsum : ((a + b : Nat) : Int) ≤
      (r + 1) * twoPow99I - twoPow27I := by
    simpa only [Int.natCast_add] using h
  apply Int.ofNat_le.mp
  simp only [Int.natCast_add, Int.natCast_mul, hcast]
  simpa [twoPow99I, twoPow99N] using c160_arg_le_int hsum

theorem c160_phase_arg_le {X r : Int} (hX : 0 ≤ X)
    (hsc : (X * 7450580596923828125 + ln2kInt 160 + lnBiasI) * twoPow27I ≤
        ((r + 1) * twoPow72I - 1) * twoPow27I)
    (harg_nonneg : 0 ≤ r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)) :
    (X.toNat * lnPhaseScaleN + BIASc * twoPow27N) *
        lnErrorBoundDen + lnErrorExtraNum * twoPow99N ≤
      (r * (lnErrorBoundDen : Int) + (lnErrorBoundNum : Int)).toNat * twoPow99N := by
  have hVs0 : (X * 7450580596923828125 + ln2kInt 160 + lnBiasI) * twoPow27I =
      X * lnPhaseScaleI + lnBiasI * twoPow27I := by
    have hVs := v_scale_pos X 160 (by decide)
    simpa only [Nat.sub_self, Nat.zero_mul, Int.natCast_zero, Int.zero_mul,
      Int.add_zero, twoPow27I, lnPhaseScaleI, lnBiasI] using hVs
  rw [hVs0] at hsc
  have hXn : ((X.toNat : Nat) : Int) = X := Int.toNat_of_nonneg hX
  have hBc : ((BIASc * twoPow27N : Nat) : Int) = lnBiasI * twoPow27I := by
    simp only [Int.natCast_mul]
    rfl
  rw [← hBc] at hsc
  have er : ((r + 1) * twoPow72I - 1) * twoPow27I =
      (r + 1) * 2 ^ 99 - 2 ^ 27 := by
    unfold twoPow72I twoPow27I
    rw [Int.sub_mul, Int.mul_assoc, show ((2 : Int) ^ 72 * 2 ^ 27) = 2 ^ 99 from
      by decide]
    omega
  rw [er] at hsc
  have hscNat :
      (((X.toNat * lnPhaseScaleN : Nat) : Int) +
        ((BIASc * twoPow27N : Nat) : Int)) ≤ (r + 1) * twoPow99I - twoPow27I := by
    have hScale : ((lnPhaseScaleN : Nat) : Int) = lnPhaseScaleI := by
      unfold lnPhaseScaleN lnPhaseScaleI
      rfl
    rw [Int.natCast_mul, hXn]
    rw [hScale]
    unfold twoPow99I twoPow27I
    exact hsc
  have hcore := c160_arg_le
    (a := X.toNat * lnPhaseScaleN)
    (b := BIASc * twoPow27N) (r := r) hscNat
    (by simpa [lnErrorBoundDen, lnErrorBoundNum] using harg_nonneg)
  simpa [lnErrorBoundDen, lnErrorBoundNum, lnErrorExtraNum, lnPhaseScaleN,
    twoPow27N, twoPow99N] using hcore

theorem phase_lt_scaled_le {V T : Int} (h : V < T) :
    V * 2 ^ 27 ≤ (T - 1) * 2 ^ 27 := by
  omega

end LnFloorCert
