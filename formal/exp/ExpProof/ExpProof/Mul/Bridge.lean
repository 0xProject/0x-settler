import ExpProof.Mono.MulTree
import ExpProof.Spec.RealExp

/-!
# `mulExpRay` public-spec bridge

This file contains the scale-agnostic reductions that do not depend on the polynomial
certificates. The public magnitude bracket depends only on the concrete floor step and the two
accumulator inequalities; sign reapplication is handled separately.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open ExpRealSpec

noncomputable section

set_option maxRecDepth 100000

/-- The dynamic real pre-floor accumulator of the shared kernel body. -/
def mulAccumReal (y x : Nat) : Real :=
  (int256 (evmSub (r0MulTree y x) marginWord) : Real) /
    (2 ^ (mulShiftTree y x) : Real)

/-- The public magnitude bracket follows from the floor step, never-over accumulator bound, and
deficit-under-one accumulator bound. -/
theorem mulExpRayMagnitudeBracket_of_accum {y x m : Int} {A : Real}
    (hm_nonneg : 0 ≤ m)
    (hfloor : (m : Real) ≤ A)
    (hfloor1 : A < (m : Real) + 1)
    (hover : A ≤ mulExpRayMagnitudeTarget y x)
    (hunder : mulExpRayMagnitudeTarget y x < A + 1) :
    MulExpRayMagnitudeBracket y x m := by
  refine ⟨hm_nonneg, le_trans hfloor hover, ?_⟩
  calc mulExpRayMagnitudeTarget y x < A + 1 := hunder
    _ < ((m : Real) + 1) + 1 := by linarith
    _ = (m : Real) + 2 := by ring

/-- Sign reapplication turns a proven magnitude bracket into the signed public bracket. -/
theorem mulExpRayBracket_of_signed_magnitude {y x r m : Int}
    (hmag : MulExpRayMagnitudeBracket y x m)
    (hsign : if y < 0 then r = -m else r = m) :
    MulExpRayBracket y x r := by
  unfold MulExpRayBracket
  by_cases hy : y < 0
  · simp [hy] at hsign ⊢
    rw [hsign]
    simpa using hmag
  · simp [hy] at hsign ⊢
    rw [hsign]
    exact hmag

/-- Magnitude brackets imply the magnitude is one unit below the exact floor at worst. -/
theorem mulExpRayMagnitudeBracket_to_underByAtMostOne {y x m : Int}
    (h : MulExpRayMagnitudeBracket y x m) :
    ⌊mulExpRayMagnitudeTarget y x⌋ - 1 ≤ m := by
  obtain ⟨_, hle, hlt⟩ := h
  set A := mulExpRayMagnitudeTarget y x with hA
  have hmle : m ≤ ⌊A⌋ := Int.le_floor.mpr hle
  have hfloorle : (⌊A⌋ : Real) ≤ A := Int.floor_le A
  have hlt2 : (⌊A⌋ : Real) < (m : Real) + 2 := lt_of_le_of_lt hfloorle hlt
  have hlt2' : (⌊A⌋ : Real) < ((m + 2 : Int) : Real) := by push_cast; linarith
  have hge : ⌊A⌋ < m + 2 := by exact_mod_cast hlt2'
  omega

end

end ExpYul
