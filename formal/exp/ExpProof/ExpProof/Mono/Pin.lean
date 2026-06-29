import ExpProof.Mono.RegionMono

/-!
# The scale-point pin

At `x = 0` the body has the value `r1Tree 0 = 10^18 − 1`, one below the unit, and the `+iszero`
shell adds the final unit. Above the scale point (`int256 x > 0`) the body has already cleared
`1 + r1Tree 0 = 10^18 = r1Tree 1`: monotonicity from the canonical word `1` gives
`r1Tree 1 ≤ r1Tree x`, and the two scale-point values are decided.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-- `r1Tree 0 = 10^18 − 1` (decided). -/
theorem r1Tree_zero : r1Tree 0 = 999999999999999999 := by decide

/-- `r1Tree 1 = 10^18` (decided); the scale-point `+1` step. -/
theorem r1Tree_one : r1Tree 1 = 1000000000000000000 := by decide

/-- **The scale-point pin** (the `RegionMonotonicityFacts.pin` field), modulo the seam step: above `x = 0`
the body has cleared `1 + r1Tree 0`. -/
theorem r1Tree_pin (hseamstep : SeamStep) {x : Nat} (hx : x < 2 ^ 256)
    (hpos : 0 < int256 x) (hC0 : int256 x < int256 C0thresh) :
    1 + (r1Tree 0 : Int) ≤ (r1Tree x : Int) := by
  -- the canonical word `1` has signed value `1 ≤ int256 x`
  have h1w : (1 : Nat) < 2 ^ 256 := by norm_num
  have h1int : int256 (1 : Nat) = 1 := by decide
  have hC1 : int256 Cmask < int256 (1 : Nat) := by
    rw [h1int, int256_Cmask]; norm_num
  have hle : int256 (1 : Nat) ≤ int256 x := by rw [h1int]; omega
  -- monotonicity from `1` to `x`
  have hmono := r1Tree_region_mono hseamstep h1w hx hC1 hle hC0
  -- both values are small (`< 2^254`), so `int256` is the Nat cast
  have hrange_x : r1Tree x < 2 ^ 254 := by
    have hC1x : int256 Cmask < int256 x := lt_of_lt_of_le hC1 hle
    exact r1Tree_range hx hC1x hC0
  have hr1x_int : int256 (r1Tree x) = (r1Tree x : Int) := by
    refine int256_of_lt ?_
    have : (2 : Nat) ^ 254 < 2 ^ 255 := by norm_num
    omega
  have hr11 : r1Tree 1 = 1000000000000000000 := r1Tree_one
  have hr11_int : int256 (r1Tree 1) = (r1Tree 1 : Int) := by
    rw [hr11]; decide
  rw [hr1x_int, hr11_int] at hmono
  -- `r1Tree 1 = 10^18 = 1 + r1Tree 0`
  have hr10 : r1Tree 0 = 999999999999999999 := r1Tree_zero
  rw [hr11] at hmono
  rw [hr10]
  push_cast at hmono ⊢
  omega

end ExpYul
