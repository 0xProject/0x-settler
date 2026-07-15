import LnProof.Floor.CarryIndependent.AnalyticRuntime
import LnProof.Floor.CarryIndependent.WordRuntime

open FormalYul FormalYul.Preservation

namespace LnFloorCarry

open LnYul

noncomputable section

theorem low_runtime_core_bound {m : Nat}
    (hmlo : 2 ^ 95 ≤ m) (hmsc : m < Sc)
    (hApprox : approximationTerm m ≤ approximationBudget)
    (hHorner : hornerTerm m ≤ hornerBudget) :
    rayScale *
        ((int256 (x1W (zWord m)) : Real) / 2 ^ 99 -
          Real.log ((m : Real) / Sc)) <
      coreErrorLimit := by
  have hword := runtime_le_lowShadow hmlo hmsc
  have hanalytic := lowShadow_core_bound hmlo hmsc hApprox hHorner
  have hscaled :
      rayScale *
          ((int256 (x1W (zWord m)) : Real) / 2 ^ 99 -
            Real.log ((m : Real) / Sc)) ≤
        rayScale * (lowShadow m - Real.log ((m : Real) / Sc)) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right hword _) (by positivity)
  exact hscaled.trans_lt hanalytic

theorem high_runtime_core_bound {m : Nat}
    (hscm : Sc ≤ m) (hmhi : m < 2 ^ 96)
    (hApprox : highApproximationTerm m ≤ approximationBudget) :
    rayScale *
        ((int256 (x1W (zWord m)) : Real) / 2 ^ 99 -
          Real.log ((m : Real) / Sc)) <
      coreErrorLimit := by
  have hword := runtime_le_highShadow hscm hmhi
  have hanalytic := highShadow_core_bound hscm hmhi hApprox
  have hscaled :
      rayScale *
          ((int256 (x1W (zWord m)) : Real) / 2 ^ 99 -
            Real.log ((m : Real) / Sc)) ≤
        rayScale * (highShadow m - Real.log ((m : Real) / Sc)) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right hword _) (by positivity)
  exact hscaled.trans_lt hanalytic

theorem mantissa_runtime_core_bound {m : Nat}
    (hmlo : 2 ^ 95 ≤ m) (hmhi : m < 2 ^ 96)
    (hLowApprox : m < Sc → approximationTerm m ≤ approximationBudget)
    (hLowHorner : m < Sc → hornerTerm m ≤ hornerBudget)
    (hHighApprox : Sc ≤ m → highApproximationTerm m ≤ approximationBudget) :
    rayScale *
        ((int256 (x1W (zWord m)) : Real) / 2 ^ 99 -
          Real.log ((m : Real) / Sc)) <
      coreErrorLimit := by
  rcases lt_or_ge m Sc with hmsc | hscm
  · exact low_runtime_core_bound hmlo hmsc (hLowApprox hmsc) (hLowHorner hmsc)
  · exact high_runtime_core_bound hscm hmhi (hHighApprox hscm)

end

end LnFloorCarry
