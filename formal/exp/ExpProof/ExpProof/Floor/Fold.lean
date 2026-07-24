import ExpProof.Floor.Spec

/-!
# The runtime accumulator in closed real form

The real pre-floor accumulator is `accumReal x = (r0 − MARGIN) / 2^(67 − k)` on the `2⁶⁷` output
grid (the quotient carries the `10¹⁸·2⁶⁷` scale directly). This file peels the runtime
plumbing off it: using the proven shift-argument transport (`shiftArg_bounds_of`:
`int256 (r0 − MARGIN) = int256 r0 − MARGIN` as `Int`) and the closing-shift value
(`closing_shift`: the shift word is `67 − int256 k`, nonnegative), the accumulator takes the
closed form `((int256 r0) − MARGIN) / 2^s` with `s = 67 − int256 (kTree x)`, the form the
never-over and deficit discharges (`Floor.R0BoundHolds`) fold the octave against.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word

noncomputable section

set_option maxRecDepth 100000

/-! ## The shift-argument value and the closing shift, as real quantities -/

/-- On the region, the numeric shift argument `r0 − MARGIN` (transported to `Int` and then to
`Real`) is `(int256 r0) − 1`, and it is nonnegative. -/
theorem accumReal_eq {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    ∃ s : Nat, (s : Int) = 67 - int256 (kTree x) ∧
      accumReal x =
        ((int256 (r0Tree x) : Real) - (1 : Real)) /
          (2 ^ s : Real) := by
  obtain ⟨s, hseq, _, _, hsint⟩ := closing_shift hx hC hC0
  obtain ⟨hr0lo, hr0hi⟩ := r0Tree_bounds hx hC hC0
  obtain ⟨hargeq, _, _⟩ := shiftArg_bounds_of (r0 := r0Tree x) (r0Tree_lt x) hr0lo hr0hi
  refine ⟨s, hsint, ?_⟩
  unfold accumReal
  rw [hseq]
  -- the integer shift argument has the closed value `r0 − 1`
  rw [hargeq]
  push_cast
  ring

end

end ExpYul
