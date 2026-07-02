import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import ExpProof.Mono.RunBridge
import ExpProof.Mono.RangeNonneg

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
from the `evmSar` sandwich. The relation between the *real-valued* runtime accumulator `A` and the
target `E = WAD·exp(x/RAY)` — never-over `A ≤ E` and deficit-under-one `E < A + 1` — is not a
runtime-plumbing fact; it is discharged in `Floor.R0BoundHolds` (`accumReal_over`/`accumReal_under`:
the cert `Floor/CapsV` against the exact rational, plus the argument-granularity, reduced-argument
and Horner-truncation envelopes the `MARGIN` absorbs).
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word

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
  (int256 (evmSub (evmMul 0xde0b6b3a7640000 (r0Tree x)) 0xe17cfd91868d72d) : Real) /
    (2 ^ (evmSub 0x7e (kTree x)) : Real)

/-- On the meaningful region the body word `r1Tree x` is the integer floor of its real accumulator
`accumReal x`: `(r1Tree x : Real) ≤ accumReal x < (r1Tree x : Real) + 1`. -/
theorem r1Tree_floor_accum {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (int256 (r1Tree x) : Real) ≤ accumReal x ∧
      accumReal x < (int256 (r1Tree x) : Real) + 1 := by
  obtain ⟨s, hseq, hslo, hshi, _⟩ := closing_shift hx hC hC0
  have hr1 : r1Tree x = evmSar s (evmSub (evmMul 0xde0b6b3a7640000 (r0Tree x)) 0xe17cfd91868d72d) := by
    have : r1Tree x = evmSar (evmSub 0x7e (kTree x))
        (evmSub (evmMul 0xde0b6b3a7640000 (r0Tree x)) 0xe17cfd91868d72d) := rfl
    rw [this, hseq]
  have hWw : evmSub (evmMul 0xde0b6b3a7640000 (r0Tree x)) 0xe17cfd91868d72d < 2 ^ 256 :=
    evmSub_lt _ _
  have hfloor := sar_real_floor (W := evmSub (evmMul 0xde0b6b3a7640000 (r0Tree x)) 0xe17cfd91868d72d)
    (s := s) (by omega) hWw
  simp only at hfloor
  -- align `accumReal` (shift `evmSub 0x7e (kTree x)`) with the lemma's shift `s`
  have hAeq : accumReal x =
      (int256 (evmSub (evmMul 0xde0b6b3a7640000 (r0Tree x)) 0xe17cfd91868d72d) : Real) /
        (2 ^ s : Real) := by
    unfold accumReal; rw [hseq]
  rw [hAeq, hr1]
  exact hfloor

end

end ExpYul
