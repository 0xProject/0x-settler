import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Real.Basic

/-!
# Public `expRayToWad` real specification

The public correctness target is a fixed-point bracket around `Real.exp`. The
input `x` is a signed ray-scale exponent (an `int256`, transported here as an
`Int`); the runtime returns the wad-scale value `r` (also an `Int`). The target
is `E = 10^18 · exp(x / 10^27)`.

The global bracket is 2-wide: `r ≤ E` (never over) together with `E < r + 2`
(under by less than two output units). It pins `r` to `{⌊E⌋, ⌊E⌋ − 1}`. The
one-unit underestimation bound is `r ≥ ⌊E⌋ − 1`.

These predicates are stated over abstract `r : Int`; the EVM-side modules
discharge them for the runtime result. The arithmetic facts here are
self-contained (Mathlib floor + cast lemmas only).
-/

namespace ExpRealSpec

noncomputable section

def WAD : Nat := 10 ^ 18
def RAY : Nat := 10 ^ 27

/-- `E = 10^18 · exp(x / 10^27)`, the real target of `expRayToWad`. -/
def expRayToWadTarget (x : Int) : Real :=
  (WAD : Real) * Real.exp ((x : Real) / (RAY : Real))

/-- **Floor-or-one-less bracket.** The result never exceeds the target and is under it
by strictly less than two output units: `r ≤ E ∧ E < r + 2`. -/
def FloorOrOneLessBracket (x : Int) (r : Int) : Prop :=
  (r : Real) ≤ expRayToWadTarget x ∧ expRayToWadTarget x < (r : Real) + 2

/-- **One-unit underestimation bound.** The result underestimates by at most one output
unit: `r ≥ ⌊E⌋ − 1`. -/
def UnderByAtMostOne (x : Int) (r : Int) : Prop :=
  ⌊expRayToWadTarget x⌋ - 1 ≤ r

/-! ## Floor facts: turning the brackets into membership / equality -/

/-- A 2-wide never-over bracket forces `r ∈ {⌊E⌋, ⌊E⌋ − 1}`. -/
theorem floorOrOneLess_mem_floor {x r : Int} (h : FloorOrOneLessBracket x r) :
    r = ⌊expRayToWadTarget x⌋ ∨ r = ⌊expRayToWadTarget x⌋ - 1 := by
  obtain ⟨hle, hlt⟩ := h
  set E := expRayToWadTarget x with hE
  have hrle : r ≤ ⌊E⌋ := Int.le_floor.mpr hle
  have hfloorlt : (⌊E⌋ : Real) ≤ E := Int.floor_le E
  -- `E < r + 2` and `⌊E⌋ ≤ E` give `⌊E⌋ < r + 2`, i.e. `⌊E⌋ ≤ r + 1`.
  have hlt2 : (⌊E⌋ : Real) < (r : Real) + 2 := lt_of_le_of_lt hfloorlt hlt
  have hlt2' : (⌊E⌋ : Real) < ((r + 2 : Int) : Real) := by push_cast; linarith
  have hge : ⌊E⌋ < r + 2 := by exact_mod_cast hlt2'
  omega

/-- The floor-or-one-less bracket implies the one-unit underestimation bound. -/
theorem floorOrOneLess_to_underByAtMostOne {x r : Int} (h : FloorOrOneLessBracket x r) :
    UnderByAtMostOne x r := by
  unfold UnderByAtMostOne
  rcases floorOrOneLess_mem_floor h with heq | heq <;> omega

/-! ## Scale point: `x = 0` gives `E = WAD = 10^18` -/

theorem expRayToWadTarget_zero : expRayToWadTarget 0 = (WAD : Real) := by
  simp [expRayToWadTarget]

/-- The floor-or-one-less bracket holds at the scale point with the proven result `r = 10^18`. -/
theorem floorOrOneLess_zero : FloorOrOneLessBracket 0 (10 ^ 18) := by
  constructor <;> rw [expRayToWadTarget_zero] <;> simp [WAD]

end

end ExpRealSpec
