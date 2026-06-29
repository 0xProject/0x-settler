import ExpProof.Mono.RunBridge
import ExpProof.Mono.RangeNonneg
import ExpProof.Seam.RealExp

/-!
# Floor + branch assembly: the public `Real.exp` brackets

`run_exp_ray_to_wad_evm_eq_expTree` returns `expTree x`, the clamp/pin shell around the floored
accumulator `r1Tree x = sar(126 − k, WAD·r0 − MARGIN)`. On the meaningful region the closing shift
`s = 126 − k ∈ [63, 187]` is positive and the shift argument `arg = WAD·r0 − MARGIN` is nonnegative,
so the runtime result is exactly the integer floor `⌊arg / 2^s⌋` of the *real* pre-floor accumulator

```
A = (WAD·r0 − MARGIN) / 2^(126 − k).
```

The two floor facts `(r : Real) ≤ A` and `A < (r : Real) + 1` (i.e. `r = ⌊A⌋`) are established here
from the `evmSar` sandwich. What is not a runtime-plumbing fact — and is collected
into the single analytic obligation `RuntimeAccumBound` below — is the relation between the
*real-valued* runtime accumulator `A` and the target `E = WAD·exp(x/RAY)`:

* never-over `A ≤ E`, and
* deficit-under-one `E < A + 1` (and the sharpened `E < r + 1` on the core octave).

`RuntimeAccumBound` packages exactly those, mirroring the way `Mono.RegionMonotonicityFacts`/`Mono.SeamR0Bound`
isolate the monotonicity analytic core. Given it, this file derives the public floor brackets
(chaining the `ExpRealBridge.*_of_accum` reductions); the analytic core itself
is the cert-fold + truncation bridge (the cert `Floor/Caps` against the exact rational, plus the
reduced-argument and Horner-truncation envelopes the `MARGIN` absorbs).
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word
open ExpRealSpec

noncomputable section

set_option maxRecDepth 100000

/-! ## The closing-shift floor, unconditionally -/

/-- A nonnegative arithmetic right shift is the integer floor of the division: with `s < 256`,
`W < 2^256` and `0 ≤ int256 W`, `int256 (evmSar s W)` is `⌊int256 W / 2^s⌋`, characterised by the
floor sandwich `2^s·R ≤ int256 W < 2^s·R + 2^s`. -/
theorem sar_floor_sandwich {W s : Nat} (hs : s < 256) (hWw : W < 2 ^ 256) :
    (2 ^ s : Int) * int256 (evmSar s W) ≤ int256 W ∧
      int256 W < (2 ^ s : Int) * int256 (evmSar s W) + 2 ^ s := by
  obtain ⟨_, hlo, hhi⟩ := evmSar_sandwich hs hWw
  exact ⟨hlo, hhi⟩

/-- The real pre-floor accumulator `A = arg / 2^s` and the runtime result `r = int256 (evmSar s W)`
satisfy `(r : Real) ≤ A < (r : Real) + 1`. This is the floor step the bridge reduction takes as a
hypothesis; here it is discharged from the `evmSar` sandwich (`s < 256`). -/
theorem sar_real_floor {W s : Nat} (hs : s < 256) (hWw : W < 2 ^ 256) :
    let r : Int := int256 (evmSar s W)
    let A : Real := (int256 W : Real) / (2 ^ s : Real)
    (r : Real) ≤ A ∧ A < (r : Real) + 1 := by
  intro r A
  obtain ⟨hlo, hhi⟩ := sar_floor_sandwich hs hWw
  have hps : (0 : Real) < (2 ^ s : Real) := by positivity
  have hpcast : ((2 ^ s : Int) : Real) = (2 ^ s : Real) := by push_cast; ring
  -- transport the integer sandwich to `Real`
  have hloR : (2 ^ s : Real) * (r : Real) ≤ (int256 W : Real) := by
    have h : ((((2 ^ s : Int) * int256 (evmSar s W)) : Int) : Real) ≤ ((int256 W : Int) : Real) :=
      Int.cast_le.mpr hlo
    push_cast at h; linarith [h]
  have hhiR : (int256 W : Real) < (2 ^ s : Real) * (r : Real) + (2 ^ s : Real) := by
    have h : ((int256 W : Int) : Real) <
        ((((2 ^ s : Int) * int256 (evmSar s W) + 2 ^ s) : Int) : Real) := Int.cast_lt.mpr hhi
    push_cast at h; linarith [h]
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hps]; linarith [hloR]
  · rw [div_lt_iff₀ hps]; nlinarith [hhiR, hps]

/-! ## The runtime accumulator as a real number

For `x > 0` in the meaningful region the result is the body word, `expTree x = r1Tree x`, with
`r1Tree x = evmSar (126 − k) (WAD·r0 − MARGIN)`. Its real pre-floor accumulator is

```
A x = int256 (WAD·r0 − MARGIN) / 2^(126 − k).
```
-/

/-- The real pre-floor accumulator of the runtime body, as an explicit `Real`. -/
def accumReal (x : Nat) : Real :=
  (int256 (evmSub (evmMul 0xde0b6b3a7640000 (r0Tree x)) 0xafe527e18748a8a) : Real) /
    (2 ^ (evmSub 0x7e (kTree x)) : Real)

/-- On the meaningful region the body word `r1Tree x` is the integer floor of its real accumulator
`accumReal x`: `(r1Tree x : Real) ≤ accumReal x < (r1Tree x : Real) + 1`. -/
theorem r1Tree_floor_accum {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (int256 (r1Tree x) : Real) ≤ accumReal x ∧
      accumReal x < (int256 (r1Tree x) : Real) + 1 := by
  obtain ⟨s, hseq, hslo, hshi, _⟩ := closing_shift hx hC hC0
  have hr1 : r1Tree x = evmSar s (evmSub (evmMul 0xde0b6b3a7640000 (r0Tree x)) 0xafe527e18748a8a) := by
    have : r1Tree x = evmSar (evmSub 0x7e (kTree x))
        (evmSub (evmMul 0xde0b6b3a7640000 (r0Tree x)) 0xafe527e18748a8a) := rfl
    rw [this, hseq]
  have hWw : evmSub (evmMul 0xde0b6b3a7640000 (r0Tree x)) 0xafe527e18748a8a < 2 ^ 256 :=
    evmSub_lt _ _
  have hfloor := sar_real_floor (W := evmSub (evmMul 0xde0b6b3a7640000 (r0Tree x)) 0xafe527e18748a8a)
    (s := s) (by omega) hWw
  simp only at hfloor
  -- align `accumReal` (shift `evmSub 0x7e (kTree x)`) with the lemma's shift `s`
  have hAeq : accumReal x =
      (int256 (evmSub (evmMul 0xde0b6b3a7640000 (r0Tree x)) 0xafe527e18748a8a) : Real) /
        (2 ^ s : Real) := by
    unfold accumReal; rw [hseq]
  rw [hAeq, hr1]
  exact hfloor

/-! ## The analytic obligation: the runtime accumulator brackets `E`

`RuntimeAccumBound` packages the relation between the real pre-floor accumulator `accumReal x` and
the public target `E = expRayToWadTarget x` that the cert-fold + truncation bridge must establish:

* `over` — never over: `accumReal x ≤ E` for any region input;
* `under` — deficit under one: `E < accumReal x + 1` for any region input;
* `centralExactness` — the sharpened core-octave bound `E < (r1Tree x : Real) + 1` (the negligible `k = 0`
  margin floors `E` exactly), for inputs in the core band `[−H, H)`.

It is the floor-side analogue of `Mono.RegionMonotonicityFacts`/`Mono.SeamR0Bound`: every runtime-plumbing and
floor fact is proved directly; the public floor brackets depend on this single
analytic core (the cert against the exact rational `ê(t) = NUM/DEN` folded with the octave `2^k`,
together with the reduced-argument `(x/RAY − k·ln2)` ≈ `tTree/2¹²⁸` envelope and the Horner-`sdiv`
truncation envelope — all absorbed by the `MARGIN`). -/
structure RuntimeAccumBound : Prop where
  /-- Never over: the real pre-floor accumulator does not exceed the target. Holds for any region
  input (the never-over relation `r0 ≤ exp(t)·2¹²⁶ + MARGIN/WAD` is octave-independent and
  sign-symmetric). -/
  over : ∀ x : Nat, x < 2 ^ 256 → int256 Cmask < int256 x → int256 x < int256 C0thresh →
    accumReal x ≤ expRayToWadTarget (int256 x)
  /-- Deficit under one: the target is below the accumulator plus one. -/
  under : ∀ x : Nat, x < 2 ^ 256 → int256 Cmask < int256 x → int256 x < int256 C0thresh →
    expRayToWadTarget (int256 x) < accumReal x + 1
  /-- Core-octave exactness: on the core band `x ∈ [−H, H)` the negligible `k = 0` margin floors
  `E` exactly onto the result. -/
  centralExactness : ∀ x : Nat, x < 2 ^ 256 → int256 Cmask < int256 x → int256 x < int256 C0thresh →
    -H ≤ int256 x → int256 x < H →
    expRayToWadTarget (int256 x) < (int256 (r1Tree x) : Real) + 1
  /-- Below the clamp boundary the target is below one output unit (`E < 1`), so the clamped result
  `0` is the floor. `Cmask = ⌊−18·ln10·10²⁷⌋` is the exact 0/1 boundary; `x ≤ Cmask` gives
  `x/10²⁷ ≤ −18·ln10`, hence `E = 10¹⁸·exp(x/10²⁷) ≤ 1`. -/
  belowC : ∀ x : Nat, int256 x ≤ int256 Cmask → expRayToWadTarget (int256 x) < 2

/-! ## The region floor brackets, given `RuntimeAccumBound` -/

theorem int256_C0thresh_floc : int256 C0thresh = 44014845965556527147994239713 := by
  unfold C0thresh int256; norm_num

theorem int256_H_lt_C0 : (H : Int) < int256 C0thresh := by
  rw [int256_C0thresh_floc]; unfold H; norm_num

theorem int256_zero_le_Cmask : int256 Cmask < 0 := by rw [int256_Cmask]; norm_num

/-- **Floor-or-one-less bracket on the region**, given the analytic accumulator bound: the body result
`r = int256 (r1Tree x)` satisfies `r ≤ E ∧ E < r + 2`. -/
theorem floorOrOneLessBracket_region {x : Nat} (H' : RuntimeAccumBound) (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    FloorOrOneLessBracket (int256 x) (int256 (r1Tree x)) := by
  obtain ⟨hfl, hfl1⟩ := r1Tree_floor_accum hx hC hC0
  exact ExpRealBridge.floorOrOneLessBracket_of_accum hfl hfl1
    (H'.over x hx hC hC0) (H'.under x hx hC hC0)

/-- **Exact-floor bracket on the core octave** (`x ∈ [−H, H)`), given the analytic accumulator
bound: `r ≤ E ∧ E < r + 1`. -/
theorem exactFloorBracket_region {x : Nat} (H' : RuntimeAccumBound) (hx : x < 2 ^ 256)
    (hlo : -H ≤ int256 x) (hhi : int256 x < H) :
    ExactFloorBracket (int256 x) (int256 (r1Tree x)) := by
  have hCmlt : int256 Cmask < -H := by rw [int256_Cmask]; unfold H; norm_num
  have hC : int256 Cmask < int256 x := lt_of_lt_of_le hCmlt hlo
  have hC0 : int256 x < int256 C0thresh := lt_of_lt_of_le hhi (le_of_lt int256_H_lt_C0)
  obtain ⟨hfl, _⟩ := r1Tree_floor_accum hx hC hC0
  exact ExpRealBridge.exactFloorBracket_of_accum hfl
    (H'.over x hx hC hC0) (H'.centralExactness x hx hC hC0 hlo hhi)

/-- **One-unit underestimation bound on the region**, given the analytic accumulator bound: `⌊E⌋ − 1 ≤ r`. -/
theorem underByAtMostOne_region {x : Nat} (H' : RuntimeAccumBound) (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    UnderByAtMostOne (int256 x) (int256 (r1Tree x)) :=
  ExpRealBridge.underByAtMostOne_of_floorOrOneLess (floorOrOneLessBracket_region H' hx hC hC0)

end

end ExpYul
