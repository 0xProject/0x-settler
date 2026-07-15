import LnProof.Floor.CarryIndependent.Cut

open FormalYul FormalYul.Preservation

set_option maxRecDepth 4096

namespace LnFloorCarry

open LnYul LnFloor LnFloorCert

noncomputable section

attribute [local irreducible] coreErrorRay zWord x1W lnWadToRayBody CutLeLogWadRay

private theorem body_mant_pos {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) :
    0 < mant x := by
  obtain ⟨me, hmlo, _⟩ := mant_facts h1 h2
  have hmlo' : 2 ^ 95 ≤ mant x := by
    unfold mant
    rw [me]
    exact hmlo
  exact lt_of_lt_of_le (by positivity : 0 < 2 ^ 95) hmlo'

theorem lnWadToRayBody_cut_of_core_bound {x : Nat}
    (h1 : 1 ≤ x) (h2 : x < 2 ^ 255) (hne : x ≠ 1000000000000000000)
    (hcore : coreErrorRay (mant x) (int256 (x1W (zWord (mant x)))) <
      (coreErrorNum : Real) / coreErrorDen) :
    CutLeLogWadRay (int256 (lnWadToRayBody x)) x := by
  have hm := body_mant_pos h1 h2
  obtain ⟨hc1, hc255⟩ := clz_bounds h1 h2
  have hwindow :
      (evmClz x ≤ 160 ∧ mant x * 2 ^ (160 - evmClz x) ≤ x) ∨
        (160 < evmClz x ∧ mant x = x * 2 ^ (evmClz x - 160)) := by
    by_cases hc : evmClz x ≤ 160
    · exact Or.inl ⟨hc, (mant_window_le h1 h2 hc).1⟩
    · exact Or.inr ⟨by omega, mant_window_gt h1 h2 (by omega)⟩
  obtain ⟨hbr, _⟩ := lnWadToRayBody_floor_bracket h1 h2 hne
  have hbr' :
      int256 (lnWadToRayBody x) * 2 ^ 72 ≤
        accumulatorI (int256 (x1W (zWord (mant x)))) (evmClz x) := by
    simpa [accumulatorI, BIASc] using hbr
  exact normalized_cut_of_core_bound (by omega) hm hc1 hc255 hwindow hbr' hcore

end

end LnFloorCarry
