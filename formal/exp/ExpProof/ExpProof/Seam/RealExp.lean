import Mathlib.Algebra.Order.Floor.Defs
import ExpProof.Spec.RealExp

/-!
# `expRayToWad` real bridge

The reduction from the pre-floor accumulator inequalities to the public `Real.exp` brackets
(`ExpProof.Spec.RealExp`): the never-over `A ≤ E` and not-two-below `E < A + 1` facts on the real
pre-floor accumulator `A`, together with the floor step `r = ⌊A⌋` (discharged by the `Floor`
layer), yield the public brackets by `Int.floor` reasoning.
-/

namespace ExpRealBridge

open ExpRealSpec

noncomputable section

/-! ## Pre-floor Accumulator To Public Brackets

`A` is the real pre-floor accumulator and `r = ⌊A⌋` the runtime result (the
`Floor` layer discharges `r = ⌊A⌋`). The cut conclusions are
`A ≤ E` (never over) and `E < A + 1` (not two below). -/

/-- **Floor-or-one-less reduction.** From the never-over conclusion `A ≤ E`, the
not-two-below conclusion `E < A + 1`, and the floor step `(r : Real) = ⌊A⌋` (so
`r ≤ A < r + 1`), the global 2-wide bracket holds. -/
theorem floorOrOneLessBracket_of_accum {x : Int} {r : Int} {A : Real}
    (hfloor : (r : Real) ≤ A) (hfloor1 : A < (r : Real) + 1)
    (hover : A ≤ expRayToWadTarget x)
    (hunder : expRayToWadTarget x < A + 1) :
    FloorOrOneLessBracket x r := by
  refine ⟨le_trans hfloor hover, ?_⟩
  calc expRayToWadTarget x < A + 1 := hunder
    _ < ((r : Real) + 1) + 1 := by linarith
    _ = (r : Real) + 2 := by ring

/-- **One-unit underestimation reduction.** The lower bound `r ≥ ⌊E⌋ − 1` is the
lower half of the floor-or-one-less bracket; given that bracket it follows. -/
theorem underByAtMostOne_of_floorOrOneLess {x : Int} {r : Int}
    (h : FloorOrOneLessBracket x r) : UnderByAtMostOne x r :=
  floorOrOneLess_to_underByAtMostOne h

end

end ExpRealBridge
