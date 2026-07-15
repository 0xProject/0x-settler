import LnProof.Cert.Approximation
import LnProof.Floor.CarryIndependent.ApproximationReal
import LnProof.Floor.CarryIndependent.HornerCorrelation
import LnProof.Floor.CarryIndependent.Runtime

open FormalYul FormalYul.Preservation

namespace LnFloorCarry

open LnYul

noncomputable section

private theorem approximationBudget_eq_error :
    approximationBudget =
      (approximationErrorNum : Real) / approximationErrorDen := by
  norm_num [approximationBudget, approximationErrorNum, approximationErrorDen]

theorem lowApproximationTerm_le_budget {m : Nat}
    (hmlo : 2 ^ 95 ≤ m) (hmsc : m < Sc) :
    approximationTerm m ≤ approximationBudget := by
  let u := uWord (zWord m)
  let z := (int256 (zWord m)).toNat
  obtain ⟨huMax, _, hzSquareInt⟩ := low_u_facts hmlo hmsc
  change u ≤ approximationMaxU at huMax
  change int256 (zWord m) ^ 2 < ((u : Int) + 1) * 2 ^ 104 at hzSquareInt
  obtain ⟨hi, a, hu, ha, hcert⟩ := approximationLowCover huMax
  have hzNonneg : 0 ≤ int256 (zWord m) := (low_z_facts hmlo hmsc).1
  have hzCast : (z : Int) = int256 (zWord m) := by
    exact Int.toNat_of_nonneg hzNonneg
  have hzSquare : z ^ 2 < (u + 1) * 2 ^ 104 := by
    rw [← hzCast] at hzSquareInt
    exact_mod_cast hzSquareInt
  have hbound := approximationLowCell_implies_series_bound
    ha hu huMax hzSquare hcert
  have hzCastReal : (z : Real) = (int256 (zWord m) : Real) := by
    exact_mod_cast hzCast
  rw [hzCastReal] at hbound
  have hray : (rayScale : Real) = 10 ^ 27 := by norm_num [rayScale]
  have hq100 : (wordQ100 : Real) = 2 ^ 100 := by norm_num [wordQ100]
  have hq96 : (wordQ96 : Real) = approximationScale := by
    norm_num [wordQ96, approximationScale]
  have hp : (pScale : Real) = 2 ^ 358 := by norm_num [pScale]
  have hq : (qScale : Real) = 2 ^ 386 := by norm_num [qScale]
  simpa [approximationTerm, normalizedZ, normalizedU, exactRatio, exactP,
    exactD, atanhSeries, approximationBudget_eq_error, hray, hq100, hq96,
    hp, hq, u] using hbound

theorem highApproximationTerm_le_budget {m : Nat}
    (hscm : Sc ≤ m) (hmhi : m < 2 ^ 96) :
    highApproximationTerm m ≤ approximationBudget := by
  let u := uWord (zWord m)
  let z := (-int256 (zWord m)).toNat
  obtain ⟨huMax, _, hzSquareInt⟩ := high_u_facts hscm hmhi
  change u ≤ approximationMaxU at huMax
  change int256 (zWord m) ^ 2 < ((u : Int) + 1) * 2 ^ 104 at hzSquareInt
  obtain ⟨hi, a, hu, ha, hcert⟩ := approximationHighCover huMax
  have hzNonneg : 0 ≤ -int256 (zWord m) :=
    neg_nonneg.mpr (high_z_facts hscm hmhi).2
  have hzCast : (z : Int) = -int256 (zWord m) := by
    exact Int.toNat_of_nonneg hzNonneg
  have hzSquare : z ^ 2 < (u + 1) * 2 ^ 104 := by
    have hzSquareCast : (z : Int) ^ 2 = int256 (zWord m) ^ 2 := by
      rw [hzCast]
      ring
    rw [← hzSquareCast] at hzSquareInt
    exact_mod_cast hzSquareInt
  have hbound := approximationHighCell_implies_series_bound
    ha hu huMax hzSquare hcert
  have hzCastReal : (z : Real) = (-int256 (zWord m) : Int) := by
    exact_mod_cast hzCast
  rw [hzCastReal] at hbound
  have hray : (rayScale : Real) = 10 ^ 27 := by norm_num [rayScale]
  have hq100 : (wordQ100 : Real) = 2 ^ 100 := by norm_num [wordQ100]
  have hq96 : (wordQ96 : Real) = approximationScale := by
    norm_num [wordQ96, approximationScale]
  have hp : (pScale : Real) = 2 ^ 358 := by norm_num [pScale]
  have hq : (qScale : Real) = 2 ^ 386 := by norm_num [qScale]
  simpa [highApproximationTerm, highNormalizedZ, normalizedU, exactRatio,
    exactP, exactD, atanhSeries, approximationBudget_eq_error, hray, hq100,
    hq96, hp, hq, u] using hbound

theorem certified_mantissa_runtime_core_bound {m : Nat}
    (hmlo : 2 ^ 95 ≤ m) (hmhi : m < 2 ^ 96) :
    rayScale *
        ((int256 (x1W (zWord m)) : Real) / 2 ^ 99 -
          Real.log ((m : Real) / Sc)) <
      coreErrorLimit := by
  exact mantissa_runtime_core_bound hmlo hmhi
    (lowApproximationTerm_le_budget hmlo)
    (lowHornerTerm_le_budget hmlo)
    (fun hscm => highApproximationTerm_le_budget hscm hmhi)

end

end LnFloorCarry
