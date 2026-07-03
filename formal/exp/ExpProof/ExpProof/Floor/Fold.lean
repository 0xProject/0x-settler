import ExpProof.Floor.Spec

/-!
# The runtime accumulator in closed real form

The real pre-floor accumulator is `accumReal x = (WAD·r0 − MARGIN) / 2^(108 − k)` on the `5¹⁸·2¹⁰⁸`
grid (`WAD = 5¹⁸`, the wad unit's `2¹⁸` folded into the closing shift). This file peels the runtime
plumbing off it: using the proven shift-argument transport (`shiftArg_bounds_of`:
`int256 (WAD·r0 − MARGIN) = WAD·r0 − MARGIN` as `Int`) and the closing-shift value
(`closing_shift`: the shift word is `108 − int256 k`, nonnegative), the accumulator takes the
closed form `(WAD·(int256 r0) − MARGIN) / 2^s` with `s = 108 − int256 (kTree x)`, the form the
never-over and deficit discharges (`Floor.R0BoundHolds`) fold the octave against.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word

noncomputable section

set_option maxRecDepth 100000

/-! ## The shift-argument value and the closing shift, as real quantities -/

/-- On the region, the numeric shift argument `WAD·r0 − MARGIN` (transported to `Int` and then to
`Real`) is `WAD·(int256 r0) − MARGIN`, and it is nonnegative. -/
theorem accumReal_eq {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    ∃ s : Nat, (s : Int) = 108 - int256 (kTree x) ∧
      accumReal x =
        ((3814697265625 : Real) * (int256 (r0Tree x) : Real) - (2209676553221 : Real)) /
          (2 ^ s : Real) := by
  obtain ⟨s, hseq, _, _, hsint⟩ := closing_shift hx hC hC0
  obtain ⟨hr0lo, hr0hi⟩ := r0Tree_bounds hx hC hC0
  obtain ⟨hargeq, _, _⟩ := shiftArg_bounds_of (r0 := r0Tree x) (r0Tree_lt x) hr0lo hr0hi
  refine ⟨s, hsint, ?_⟩
  unfold accumReal
  rw [hseq]
  -- the integer shift argument has the closed value `WAD·r0 − MARGIN`
  have hwadc : (0x3782dace9d9 : Int) = 3814697265625 := by norm_num
  have hmarc : (0x2027afc6c05 : Int) = 2209676553221 := by norm_num
  rw [hargeq, hwadc, hmarc]
  push_cast
  ring

end

end ExpYul
