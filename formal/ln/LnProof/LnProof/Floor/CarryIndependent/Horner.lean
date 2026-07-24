import LnProof.Floor.CarryIndependent.Bounds

namespace LnFloorCarry

open Common.Poly LnYul

noncomputable section

theorem hornerTerm_le_of_gap_le {m : Nat} {bound : Real}
    (hz0 : 0 ≤ normalizedZ m) (hzEnd : normalizedZ m ≤ endpointZ)
    (hbound : 0 ≤ bound)
    (hgap : exactRatio (uWord (zWord m)) -
        shadowRatio (uWord (zWord m)) ≤ bound) :
    hornerTerm m ≤ 2 * rayScale * endpointZ * bound := by
  have hscale : (0 : Real) ≤ 2 * rayScale := by norm_num [rayScale]
  have hscaledZ : 0 ≤ 2 * rayScale * normalizedZ m :=
    mul_nonneg hscale hz0
  have hzScaled : 2 * rayScale * normalizedZ m ≤
      2 * rayScale * endpointZ :=
    mul_le_mul_of_nonneg_left hzEnd hscale
  unfold hornerTerm
  calc
    2 * rayScale * normalizedZ m *
          (exactRatio (uWord (zWord m)) -
            shadowRatio (uWord (zWord m))) ≤
        2 * rayScale * normalizedZ m * bound := by
      exact mul_le_mul_of_nonneg_left hgap hscaledZ
    _ ≤ 2 * rayScale * endpointZ * bound := by
      exact mul_le_mul_of_nonneg_right hzScaled hbound

theorem ratio_le_endpoint_of_cross_nonneg
    {num den : List Int} {u endpoint : Int}
    (hden : 0 < evalPoly den u)
    (hEndpointDen : 0 < evalPoly den endpoint)
    (hcross :
      0 ≤ evalPoly num endpoint * evalPoly den u -
        evalPoly den endpoint * evalPoly num u) :
    (evalPoly num u : Real) / evalPoly den u ≤
      (evalPoly num endpoint : Real) / evalPoly den endpoint := by
  have hcrossInt :
      evalPoly num u * evalPoly den endpoint ≤
        evalPoly num endpoint * evalPoly den u := by
    simpa only [mul_comm] using sub_nonneg.mp hcross
  have hcrossReal :
      (evalPoly num u : Real) * evalPoly den endpoint ≤
        evalPoly num endpoint * evalPoly den u := by
    exact_mod_cast hcrossInt
  rw [div_le_div_iff₀ (by exact_mod_cast hden) (by exact_mod_cast hEndpointDen)]
  exact hcrossReal

end

end LnFloorCarry
