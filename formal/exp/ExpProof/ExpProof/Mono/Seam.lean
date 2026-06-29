import ExpProof.Mono.RegionMono

/-!
# The octave-seam step from the `r0` doubling bound

Across a seam (`k` advances by one, `int256 x2 = int256 x1 + 1`) the closing shift `126 − k` drops
exactly one bit, so with the same shift argument `arg = WAD·r0 − MARGIN` the floor identity

```
r1Tree x2 = ⌊arg2 / 2^(s−1)⌋ = ⌊2·arg2 / 2^s⌋ ≥ ⌊arg1 / 2^s⌋ = r1Tree x1   ⟸   arg1 ≤ 2·arg2
```

reduces the seam step to `arg1 ≤ 2·arg2`, which (since `MARGIN < WAD`) follows from the **`r0`
doubling bound** `r0Tree x1 < 2·r0Tree x2` (`SeamR0Bound`). The reduction is assembled over the
opaque shift-argument words (`seam_close`), so the deep `evmSar`/`evmSub`/`evmMul` tree behind
`r1Tree` is never forced into whnf.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-- **The `r0` doubling bound across a seam.** For adjacent inputs crossing one octave
(`int256 (kTree x2) = int256 (kTree x1) + 1`, `int256 x2 = int256 x1 + 1`), the Q126 quotient at
most doubles: `r0Tree x1 < 2·r0Tree x2`. (Across the seam the reduced argument flips sign
`t_b ≈ −t_a`, so `r0_a ≈ exp(t_a)·2^126 ≈ √2·2^126` and `r0_b ≈ exp(−t_a)·2^126 ≈ 2^126/√2`, hence
`r0_a/r0_b ≈ 2`.) -/
def SeamR0Bound : Prop :=
  ∀ {x1 x2 : Nat}, x1 < 2 ^ 256 → x2 < 2 ^ 256 →
    int256 Cmask < int256 x1 → int256 x1 < int256 C0thresh →
    int256 Cmask < int256 x2 → int256 x2 < int256 C0thresh →
    int256 (kTree x2) = int256 (kTree x1) + 1 →
    int256 x2 = int256 x1 + 1 →
    int256 (r0Tree x1) < 2 * int256 (r0Tree x2)

/-- Abstract seam floor reduction over opaque shift-argument words and shift amounts. With the
closing shift dropping one bit (`s2 + 1 = s1`) and `arg1 ≤ 2·arg2`, the two arithmetic-shift floors
are `≤`-ordered: `⌊arg1 / 2^s1⌋ ≤ ⌊arg2 / 2^(s1−1)⌋`. -/
theorem seam_close {arg1 arg2 s1 s2 : Nat}
    (ha1 : arg1 < 2 ^ 256) (ha2 : arg2 < 2 ^ 256)
    (hs1 : s1 < 256) (hs2 : s2 < 256) (hseq : s2 + 1 = s1)
    (hle : int256 arg1 ≤ 2 * int256 arg2) :
    int256 (evmSar s1 arg1) ≤ int256 (evmSar s2 arg2) := by
  obtain ⟨_, hsl1, _⟩ := evmSar_sandwich (s := s1) hs1 ha1
  obtain ⟨_, _, hsh2⟩ := evmSar_sandwich (s := s2) hs2 ha2
  have hpow : (2 : Int) ^ s1 = 2 * 2 ^ s2 := by rw [← hseq, pow_succ]; ring
  have hp2 : (0 : Int) < 2 ^ s2 := by positivity
  set R1 := int256 (evmSar s1 arg1)
  set R2 := int256 (evmSar s2 arg2)
  -- `2^s1·R1 ≤ arg1 ≤ 2·arg2 < 2·(2^s2·R2 + 2^s2) = 2^s1·R2 + 2^s1` ⇒ `R1 < R2 + 1` ⇒ `R1 ≤ R2`.
  rw [hpow] at hsl1
  nlinarith [hsl1, hsh2, hle, hp2]

/-- The closing shifts at a seam differ by one (`s2 = s1 − 1`), both in `[63, 187]`. -/
theorem seam_closing_shifts {x1 x2 : Nat}
    (hx1 : x1 < 2 ^ 256) (hC1 : int256 Cmask < int256 x1) (hC01 : int256 x1 < int256 C0thresh)
    (hx2 : x2 < 2 ^ 256) (hC2 : int256 Cmask < int256 x2) (hC02 : int256 x2 < int256 C0thresh)
    (hk : int256 (kTree x2) = int256 (kTree x1) + 1) :
    ∃ s1 s2 : Nat, evmSub 0x7e (kTree x1) = s1 ∧ evmSub 0x7e (kTree x2) = s2 ∧
      s1 < 256 ∧ s2 < 256 ∧ s2 + 1 = s1 := by
  obtain ⟨s1, hs1eq, _, hs1hi, hs1int⟩ := closing_shift hx1 hC1 hC01
  obtain ⟨s2, hs2eq, hs2lo, _, hs2int⟩ := closing_shift hx2 hC2 hC02
  refine ⟨s1, s2, hs1eq, hs2eq, by omega, by omega, ?_⟩
  -- `(s2 : Int) + 1 = 126 − k2 + 1 = 126 − k1 = (s1 : Int)`
  have : (s2 : Int) + 1 = (s1 : Int) := by rw [hs1int, hs2int, hk]; ring
  omega

/-- **The octave-seam step from the `r0` doubling bound.** Given `SeamR0Bound`, the closing
accumulator is nondecreasing across a seam. The shift arguments are named opaquely before the
floor lemma, so the deep tree behind `r1Tree` is never reduced. -/
theorem seamStep_of_r0 (hr0 : SeamR0Bound) {x1 x2 : Nat} (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hC1 : int256 Cmask < int256 x1) (hC01 : int256 x1 < int256 C0thresh)
    (hC2 : int256 Cmask < int256 x2) (hC02 : int256 x2 < int256 C0thresh)
    (hk : int256 (kTree x2) = int256 (kTree x1) + 1)
    (hadj : int256 x2 = int256 x1 + 1) :
    int256 (r1Tree x1) ≤ int256 (r1Tree x2) := by
  obtain ⟨s1, s2, hs1eq, hs2eq, hs1lt, hs2lt, hseq⟩ :=
    seam_closing_shifts hx1 hC1 hC01 hx2 hC2 hC02 hk
  obtain ⟨hr0lo1, hr0hi1⟩ := r0Tree_bounds hx1 hC1 hC01
  obtain ⟨hr0lo2, hr0hi2⟩ := r0Tree_bounds hx2 hC2 hC02
  obtain ⟨harg1eq, _, _⟩ := shiftArg_bounds_of (r0 := r0Tree x1) (r0Tree_lt x1) hr0lo1 hr0hi1
  obtain ⟨harg2eq, _, _⟩ := shiftArg_bounds_of (r0 := r0Tree x2) (r0Tree_lt x2) hr0lo2 hr0hi2
  have hr1eq1 : r1Tree x1 =
      evmSar s1 (evmSub (evmMul 0xde0b6b3a7640000 (r0Tree x1)) 0xafe527e18748a8a) := by
    unfold r1Tree; rw [hs1eq]
  have hr1eq2 : r1Tree x2 =
      evmSar s2 (evmSub (evmMul 0xde0b6b3a7640000 (r0Tree x2)) 0xafe527e18748a8a) := by
    unfold r1Tree; rw [hs2eq]
  rw [hr1eq1, hr1eq2]
  -- name the deep shift arguments opaquely before feeding the floor lemma
  set arg1 := evmSub (evmMul 0xde0b6b3a7640000 (r0Tree x1)) 0xafe527e18748a8a with harg1def
  set arg2 := evmSub (evmMul 0xde0b6b3a7640000 (r0Tree x2)) 0xafe527e18748a8a with harg2def
  have hr0bound : int256 (r0Tree x1) < 2 * int256 (r0Tree x2) :=
    hr0 hx1 hx2 hC1 hC01 hC2 hC02 hk hadj
  have hargle : int256 arg1 ≤ 2 * int256 arg2 := by
    rw [harg1eq, harg2eq, show (0xde0b6b3a7640000 : Int) = 1000000000000000000 by norm_num,
      show (0xafe527e18748a8a : Int) = 792161285993433738 by norm_num]
    -- `WAD·r0a − M ≤ 2·(WAD·r0b − M)` ⟸ `WAD·r0a + M ≤ 2·WAD·r0b` ⟸ `r0a ≤ 2·r0b − 1` and `M ≤ WAD`
    nlinarith [hr0bound]
  exact seam_close (harg1def ▸ evmSub_lt _ _) (harg2def ▸ evmSub_lt _ _) hs1lt hs2lt hseq hargle

/-- The seam step (`SeamStep`) follows from the `r0` doubling bound. -/
theorem seamStep_of_seamR0 (hr0 : SeamR0Bound) : SeamStep :=
  fun hx1 hx2 hC1 hC01 hC2 hC02 hk hadj =>
    seamStep_of_r0 hr0 hx1 hx2 hC1 hC01 hC2 hC02 hk hadj

end ExpYul
