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

/-! ## `mulExpRay` magnitude target -/

/-- `A = abs(y) · exp(x / 10^27)`, the nonnegative real magnitude target of `mulExpRay`. -/
def mulExpRayMagnitudeTarget (y x : Int) : Real :=
  (y.natAbs : Real) * Real.exp ((x : Real) / (RAY : Real))

/-- **Magnitude floor-or-one-less bracket.** The nonnegative magnitude result never exceeds the
target magnitude and is under it by strictly less than two output units. -/
def MulExpRayMagnitudeBracket (y x m : Int) : Prop :=
  0 ≤ m ∧ (m : Real) ≤ mulExpRayMagnitudeTarget y x ∧
    mulExpRayMagnitudeTarget y x < (m : Real) + 2

/-- **Signed magnitude bracket.** The runtime result is interpreted by removing `y`'s sign before
checking the magnitude bracket. -/
def MulExpRayBracket (y x r : Int) : Prop :=
  if y < 0 then MulExpRayMagnitudeBracket y x (-r) else MulExpRayMagnitudeBracket y x r

/-- The exact real target of `mulExpRay`, including sign. -/
def mulExpRayTarget (y x : Int) : Real :=
  (y : Real) * Real.exp ((x : Real) / (RAY : Real))

/-- Monotonicity in `x` follows `y`'s sign: positive magnitudes are nondecreasing, negative
magnitudes are nonincreasing, and zero is constant. -/
def MulExpRaySignedMonotone (y x1 x2 r1 r2 : Int) : Prop :=
  x1 ≤ x2 ∧ if y < 0 then r2 ≤ r1 else r1 ≤ r2

/-- Monotonicity in `y`: at a fixed exponent, signed results are nondecreasing in signed
multiplier order. -/
def MulExpRayYMonotone (y1 y2 _x r1 r2 : Int) : Prop :=
  y1 ≤ y2 ∧ r1 ≤ r2

/-- Joint monotonicity is sign-aware: nonnegative multipliers move with `x`, nonpositive
multipliers move against `x`, and sign-crossing multipliers are ordered for any exponents. -/
def MulExpRayJointMonotone (y1 y2 x1 x2 r1 r2 : Int) : Prop :=
  ((0 ≤ y1 ∧ y1 ≤ y2 ∧ x1 ≤ x2) ∨
    (y1 ≤ y2 ∧ y2 ≤ 0 ∧ x2 ≤ x1) ∨
    (y1 ≤ 0 ∧ 0 ≤ y2)) ∧
    r1 ≤ r2

theorem mulExpRayMagnitudeTarget_nonneg (y x : Int) :
    0 ≤ mulExpRayMagnitudeTarget y x := by
  unfold mulExpRayMagnitudeTarget
  positivity

theorem mulExpRayMagnitudeTarget_mono {y x1 x2 : Int} (hle : x1 ≤ x2) :
    mulExpRayMagnitudeTarget y x1 ≤ mulExpRayMagnitudeTarget y x2 := by
  unfold mulExpRayMagnitudeTarget
  have hR : (0 : Real) ≤ (RAY : Real) := by norm_num [RAY]
  have hx : ((x1 : Real) / (RAY : Real)) ≤ ((x2 : Real) / (RAY : Real)) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hle) hR
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx) (by positivity)

theorem mulExpRayTarget_mono_nonneg {y x1 x2 : Int} (hy : 0 ≤ y) (hle : x1 ≤ x2) :
    mulExpRayTarget y x1 ≤ mulExpRayTarget y x2 := by
  unfold mulExpRayTarget
  have hR : (0 : Real) ≤ (RAY : Real) := by norm_num [RAY]
  have hx : ((x1 : Real) / (RAY : Real)) ≤ ((x2 : Real) / (RAY : Real)) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hle) hR
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx) (by exact_mod_cast hy)

theorem mulExpRayTarget_antitone_neg {y x1 x2 : Int} (hy : y < 0) (hle : x1 ≤ x2) :
    mulExpRayTarget y x2 ≤ mulExpRayTarget y x1 := by
  unfold mulExpRayTarget
  have hR : (0 : Real) ≤ (RAY : Real) := by norm_num [RAY]
  have hx : ((x1 : Real) / (RAY : Real)) ≤ ((x2 : Real) / (RAY : Real)) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hle) hR
  exact mul_le_mul_of_nonpos_left (Real.exp_le_exp.mpr hx) (by exact_mod_cast (le_of_lt hy))

theorem mulExpRayTarget_antitone_nonpos {y x1 x2 : Int} (hy : y ≤ 0) (hle : x1 ≤ x2) :
    mulExpRayTarget y x2 ≤ mulExpRayTarget y x1 := by
  unfold mulExpRayTarget
  have hR : (0 : Real) ≤ (RAY : Real) := by norm_num [RAY]
  have hx : ((x1 : Real) / (RAY : Real)) ≤ ((x2 : Real) / (RAY : Real)) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hle) hR
  exact mul_le_mul_of_nonpos_left (Real.exp_le_exp.mpr hx) (by exact_mod_cast hy)

theorem mulExpRayTarget_signed_mono {y x1 x2 : Int} (hle : x1 ≤ x2) :
    if y < 0 then mulExpRayTarget y x2 ≤ mulExpRayTarget y x1
    else mulExpRayTarget y x1 ≤ mulExpRayTarget y x2 := by
  by_cases hy : y < 0
  · simp [hy, mulExpRayTarget_antitone_neg hy hle]
  · have hy0 : 0 ≤ y := by omega
    simp [hy, mulExpRayTarget_mono_nonneg hy0 hle]

theorem mulExpRayTarget_mono_y {y1 y2 x : Int} (hle : y1 ≤ y2) :
    mulExpRayTarget y1 x ≤ mulExpRayTarget y2 x := by
  unfold mulExpRayTarget
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (le_of_lt (Real.exp_pos _))

theorem mulExpRayTarget_nonpos_of_nonpos_y {y x : Int} (hy : y ≤ 0) :
    mulExpRayTarget y x ≤ 0 := by
  unfold mulExpRayTarget
  exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hy) (le_of_lt (Real.exp_pos _))

theorem mulExpRayTarget_nonneg_of_nonneg_y {y x : Int} (hy : 0 ≤ y) :
    0 ≤ mulExpRayTarget y x := by
  unfold mulExpRayTarget
  exact mul_nonneg (by exact_mod_cast hy) (le_of_lt (Real.exp_pos _))

theorem mulExpRayTarget_joint_mono {y1 y2 x1 x2 : Int}
    (h :
      (0 ≤ y1 ∧ y1 ≤ y2 ∧ x1 ≤ x2) ∨
      (y1 ≤ y2 ∧ y2 ≤ 0 ∧ x2 ≤ x1) ∨
      (y1 ≤ 0 ∧ 0 ≤ y2)) :
    mulExpRayTarget y1 x1 ≤ mulExpRayTarget y2 x2 := by
  rcases h with ⟨hy1, hy, hx⟩ | ⟨hy, hy2, hx⟩ | ⟨hy1, hy2⟩
  · exact le_trans (mulExpRayTarget_mono_nonneg hy1 hx) (mulExpRayTarget_mono_y hy)
  · have hy1 : y1 ≤ 0 := le_trans hy hy2
    exact le_trans (mulExpRayTarget_antitone_nonpos hy1 hx) (mulExpRayTarget_mono_y hy)
  · exact le_trans (mulExpRayTarget_nonpos_of_nonpos_y hy1)
      (mulExpRayTarget_nonneg_of_nonneg_y hy2)

theorem mulExpRayMagnitudeBracket_zero (x r : Int) (hr : r = 0) :
    MulExpRayMagnitudeBracket 0 x r := by
  subst hr
  constructor
  · norm_num
  · constructor
    · simp [mulExpRayMagnitudeTarget]
    · simp [mulExpRayMagnitudeTarget]

end

end ExpRealSpec
