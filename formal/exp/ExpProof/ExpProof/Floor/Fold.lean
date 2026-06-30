import ExpProof.Floor.Spec

/-!
# Reducing the accumulator bound to a clean `r0`-vs-`exp` bound

`RuntimeAccumBound` (the obligation `Floor.Public` carries) is about the real pre-floor accumulator
`accumReal x = (WAD·r0 − MARGIN) / 2^(126 − k)`. This file peels the runtime plumbing off it: using
the proven shift-argument transport (`shiftArg_bounds_of`: `int256 (WAD·r0 − MARGIN) = WAD·r0 − MARGIN`
as `Int`) and the closing-shift value (`closing_shift`: the shift word is `126 − int256 k`,
nonnegative), the never-over and deficit inequalities collapse to *octave-folded* `r0` bounds against
the target.

Writing `s = 126 − int256 (kTree x) ≥ 0`, `WAD = 10¹⁸`, `MARGIN = 0x9fe769d0fa58e9f`, the algebra is:

```
accumReal x ≤ E   ⟺   WAD·r0 − MARGIN ≤ E·2^s
E < accumReal x + 1   ⟺   E·2^s < WAD·r0 − MARGIN + 2^s
```

with `E = expRayToWadTarget x`. `RuntimeR0Bound` packages exactly those two inequalities, so a
discharge of it gives `RuntimeAccumBound.over`/`under`
directly. The analytic content of `RuntimeR0Bound` — `r0Tree x ≈ exp(x/10²⁷)·2^126/2^k`
within the `MARGIN` envelope — is the cert (`Floor.CapsV`, against `ê = NUM/DEN`) folded with the
octave `2^k` together with the reduced-argument and Horner-`sdiv` truncation envelopes; this module
performs only the (unconditional, axiom-clean) plumbing reduction.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word
open ExpRealSpec

noncomputable section

set_option maxRecDepth 100000

/-! ## The shift-argument value and the closing shift, as real quantities -/

/-- On the region, the numeric shift argument `WAD·r0 − MARGIN` (transported to `Int` and then to
`Real`) is `WAD·(int256 r0) − MARGIN`, and it is nonnegative. -/
theorem accumReal_eq {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    ∃ s : Nat, (s : Int) = 126 - int256 (kTree x) ∧
      accumReal x =
        ((10 ^ 18 : Real) * (int256 (r0Tree x) : Real) - (720143407370309279 : Real)) /
          (2 ^ s : Real) := by
  obtain ⟨s, hseq, _, _, hsint⟩ := closing_shift hx hC hC0
  obtain ⟨hr0lo, hr0hi⟩ := r0Tree_bounds hx hC hC0
  obtain ⟨hargeq, _, _⟩ := shiftArg_bounds_of (r0 := r0Tree x) (r0Tree_lt x) hr0lo hr0hi
  refine ⟨s, hsint, ?_⟩
  unfold accumReal
  rw [hseq]
  -- the integer shift argument has the closed value `WAD·r0 − MARGIN`
  have hwadc : (0xde0b6b3a7640000 : Int) = 1000000000000000000 := by norm_num
  have hmarc : (0x9fe769d0fa58e9f : Int) = 720143407370309279 := by norm_num
  rw [hargeq, hwadc, hmarc]
  push_cast
  ring

/-! ## The clean octave-folded `r0` bound

`RuntimeR0Bound` is the elementary statement the cert-fold + truncation bridge must establish: with
`s = 126 − int256 k` the closing shift, the floored accumulator brackets `E`. Phrasing it directly
on `WAD·r0 − MARGIN` vs `E·2^s` keeps it free of any `Real.exp` octave-fold bookkeeping — that
bookkeeping is internal to the eventual discharge (the `2^k` is `2^(126 − s)` here). -/
structure RuntimeR0Bound : Prop where
  /-- Never over: `WAD·r0 − MARGIN ≤ E·2^(126 − k)`. -/
  over : ∀ x : Nat, x < 2 ^ 256 → int256 Cmask < int256 x → int256 x < int256 C0thresh →
    ∀ s : Nat, (s : Int) = 126 - int256 (kTree x) →
      (10 ^ 18 : Real) * (int256 (r0Tree x) : Real) - 720143407370309279 ≤
        expRayToWadTarget (int256 x) * (2 ^ s : Real)
  /-- Deficit under one: `E·2^(126 − k) < WAD·r0 − MARGIN + 2^(126 − k)`. -/
  under : ∀ x : Nat, x < 2 ^ 256 → int256 Cmask < int256 x → int256 x < int256 C0thresh →
    ∀ s : Nat, (s : Int) = 126 - int256 (kTree x) →
      expRayToWadTarget (int256 x) * (2 ^ s : Real) <
        (10 ^ 18 : Real) * (int256 (r0Tree x) : Real) - 720143407370309279 + (2 ^ s : Real)
  /-- Below the clamp boundary `E < 1` (carried through verbatim). -/
  belowC : ∀ x : Nat, int256 x ≤ int256 Cmask → expRayToWadTarget (int256 x) < 1

/-- **The plumbing reduction.** `RuntimeR0Bound` discharges `RuntimeAccumBound`: the never-over and
deficit inequalities transport across the closing shift `2^s > 0`. -/
theorem runtimeAccumBound_of_r0 (H : RuntimeR0Bound) : RuntimeAccumBound where
  over := fun x hx hC hC0 => by
    obtain ⟨s, hsint, hAeq⟩ := accumReal_eq hx hC hC0
    have hps : (0 : Real) < (2 ^ s : Real) := by positivity
    have hb := H.over x hx hC hC0 s hsint
    rw [hAeq, div_le_iff₀ hps]
    linarith [hb]
  under := fun x hx hC hC0 => by
    obtain ⟨s, hsint, hAeq⟩ := accumReal_eq hx hC hC0
    have hps : (0 : Real) < (2 ^ s : Real) := by positivity
    have hb := H.under x hx hC hC0 s hsint
    -- goal `E < accumReal x + 1`; rewrite `accumReal` and clear the `/2^s`
    rw [hAeq]
    -- `E < arg/2^s + 1`  ⟺  `E·2^s < arg + 2^s`
    have key : expRayToWadTarget (int256 x) * (2 ^ s : Real) <
        ((10 ^ 18 : Real) * (int256 (r0Tree x) : Real) - 720143407370309279) + (2 ^ s : Real) :=
      hb
    have hdiv : ((10 ^ 18 : Real) * (int256 (r0Tree x) : Real) - 720143407370309279) /
        (2 ^ s : Real) + 1 =
        (((10 ^ 18 : Real) * (int256 (r0Tree x) : Real) - 720143407370309279) + (2 ^ s : Real)) /
          (2 ^ s : Real) := by
      field_simp
    rw [hdiv, lt_div_iff₀ hps]
    linarith [key]
  belowC := fun x hxle => H.belowC x hxle

end

end ExpYul
