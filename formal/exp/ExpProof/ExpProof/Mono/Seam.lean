import ExpProof.Mono.RegionMono

/-!
# The octave-seam step from the `r0` doubling bound

Across a seam (`k` advances by one, `int256 x2 = int256 x1 + 1`) the closing shift `68 − k` drops
exactly one bit, so with the same shift argument `arg = r0 − MARGIN` the floor identity

```
r1Tree x2 = ⌊arg2 / 2^(s−1)⌋ = ⌊2·arg2 / 2^s⌋ ≥ ⌊arg1 / 2^s⌋ = r1Tree x1   ⟸   arg1 ≤ 2·arg2
```

reduces the seam step to `arg1 ≤ 2·arg2`, which follows from the **`r0` doubling bound**
`r0Tree x1 + 3 ≤ 2·r0Tree x2` (`SeamR0Bound`; three integer units of the doubling gap cover the
subtracted margin). The reduction is assembled over the
opaque shift-argument words (`seam_close`), so the deep `evmShr`/`evmSub`/`evmMul` tree behind
`r1Tree` is never forced into whnf.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-- **The `r0` doubling bound across a seam.** For adjacent inputs crossing one octave
(`int256 (kTree x2) = int256 (kTree x1) + 1`, `int256 x2 = int256 x1 + 1`), the scaled quotient at
most doubles, three units short: `r0Tree x1 + 3 ≤ 2·r0Tree x2`. (Across the seam the reduced
argument flips sign `t_b ≈ −t_a`, so `r0_a ≈ exp(t_a)·scaleQ68 ≈ √2·scaleQ68` and
`r0_b ≈ exp(−t_a)·scaleQ68 ≈ scaleQ68/√2`, hence `r0_a/r0_b ≈ 2·exp(−1/RAY)`, short of doubling by
`≈ 2·r0_b/RAY ≈ 4·10^11` grid units — far more than the three units consumed by the seam-floor
comparison below.) -/
def SeamR0Bound : Prop :=
  ∀ {x1 x2 : Nat}, x1 < 2 ^ 256 → x2 < 2 ^ 256 →
    int256 Cmask < int256 x1 → int256 x1 < int256 C0thresh →
    int256 Cmask < int256 x2 → int256 x2 < int256 C0thresh →
    int256 (kTree x2) = int256 (kTree x1) + 1 →
    int256 x2 = int256 x1 + 1 →
    int256 (r0Tree x1) + 3 ≤ 2 * int256 (r0Tree x2)

/-- Abstract seam floor reduction over opaque nonnegative shift-argument words and shift amounts.
With the closing shift dropping one bit (`s2 + 1 = s1`) and `arg1 ≤ 2·arg2`, the two logical-shift
floors are `≤`-ordered: `⌊arg1 / 2^s1⌋ ≤ ⌊arg2 / 2^(s1−1)⌋`. -/
theorem seam_close {arg1 arg2 s1 s2 : Nat}
    (ha1 : arg1 < 2 ^ 256) (ha2 : arg2 < 2 ^ 256)
    (hs1 : s1 < 256) (hs2 : s2 < 256) (hseq : s2 + 1 = s1)
    (hnn1 : 0 ≤ int256 arg1) (hnn2 : 0 ≤ int256 arg2)
    (hle : int256 arg1 ≤ 2 * int256 arg2) :
    int256 (evmShr s1 arg1) ≤ int256 (evmShr s2 arg2) := by
  obtain ⟨he1, hlt1⟩ := int256_eq_of_nonneg ha1 hnn1
  obtain ⟨he2, hlt2⟩ := int256_eq_of_nonneg ha2 hnn2
  have hleN : arg1 ≤ 2 * arg2 := by
    have : ((arg1 : Nat) : Int) ≤ ((2 * arg2 : Nat) : Int) := by
      rw [← he1]; push_cast; rw [← he2]; exact hle
    exact_mod_cast this
  rw [evmShr_eq_div hs1 ha1, evmShr_eq_div hs2 ha2]
  -- ⌊arg1 / 2^s1⌋ ≤ ⌊2·arg2 / 2^s1⌋ = ⌊arg2 / 2^s2⌋
  have hkey : 2 * arg2 / 2 ^ s1 = arg2 / 2 ^ s2 := by
    rw [← hseq, pow_succ, Nat.mul_comm (2 ^ s2) 2, Nat.mul_div_mul_left arg2 (2 ^ s2) (by norm_num)]
  have hqle : arg1 / 2 ^ s1 ≤ arg2 / 2 ^ s2 := by
    rw [← hkey]
    exact Nat.div_le_div_right hleN
  have hq1lt : arg1 / 2 ^ s1 < 2 ^ 255 := by
    have := Nat.div_le_self arg1 (2 ^ s1)
    omega
  have hq2lt : arg2 / 2 ^ s2 < 2 ^ 255 := by
    have := Nat.div_le_self arg2 (2 ^ s2)
    omega
  rw [int256_of_lt hq1lt, int256_of_lt hq2lt]
  exact_mod_cast hqle

/-- The closing shifts at a seam differ by one (`s2 = s1 − 1`), both in `[4, 129]`. -/
theorem seam_closing_shifts {x1 x2 : Nat}
    (hx1 : x1 < 2 ^ 256) (hC1 : int256 Cmask < int256 x1) (hC01 : int256 x1 < int256 C0thresh)
    (hx2 : x2 < 2 ^ 256) (hC2 : int256 Cmask < int256 x2) (hC02 : int256 x2 < int256 C0thresh)
    (hk : int256 (kTree x2) = int256 (kTree x1) + 1) :
    ∃ s1 s2 : Nat, evmSub 0x44 (kTree x1) = s1 ∧ evmSub 0x44 (kTree x2) = s2 ∧
      s1 < 256 ∧ s2 < 256 ∧ s2 + 1 = s1 := by
  obtain ⟨s1, hs1eq, _, hs1hi, hs1int⟩ := closing_shift hx1 hC1 hC01
  obtain ⟨s2, hs2eq, hs2lo, _, hs2int⟩ := closing_shift hx2 hC2 hC02
  refine ⟨s1, s2, hs1eq, hs2eq, by omega, by omega, ?_⟩
  -- `(s2 : Int) + 1 = 68 − k2 + 1 = 68 − k1 = (s1 : Int)`
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
  obtain ⟨harg1eq, harg1nn, _⟩ := shiftArg_bounds_of (r0 := r0Tree x1) (r0Tree_lt x1) hr0lo1 hr0hi1
  obtain ⟨harg2eq, harg2nn, _⟩ := shiftArg_bounds_of (r0 := r0Tree x2) (r0Tree_lt x2) hr0lo2 hr0hi2
  have hr1eq1 : r1Tree x1 =
      evmShr s1 (evmSub (r0Tree x1) 0x3) := by
    unfold r1Tree; rw [hs1eq]
  have hr1eq2 : r1Tree x2 =
      evmShr s2 (evmSub (r0Tree x2) 0x3) := by
    unfold r1Tree; rw [hs2eq]
  rw [hr1eq1, hr1eq2]
  -- name the deep shift arguments opaquely before feeding the floor lemma
  set arg1 := evmSub (r0Tree x1) 0x3 with harg1def
  set arg2 := evmSub (r0Tree x2) 0x3 with harg2def
  have ha1lt : arg1 < 2 ^ 256 := by rw [harg1def]; exact evmSub_lt _ _
  have ha2lt : arg2 < 2 ^ 256 := by rw [harg2def]; exact evmSub_lt _ _
  clear_value arg1 arg2
  have hr0bound : int256 (r0Tree x1) + 3 ≤ 2 * int256 (r0Tree x2) :=
    hr0 hx1 hx2 hC1 hC01 hC2 hC02 hk hadj
  have hargle : int256 arg1 ≤ 2 * int256 arg2 := by
    rw [harg1eq, harg2eq]
    -- `r0a − 3 ≤ 2·(r0b − 3)` ⟸ `r0a + 3 ≤ 2·r0b`
    linarith [hr0bound]
  exact seam_close ha1lt ha2lt hs1lt hs2lt hseq
    (by rw [harg1eq]; exact harg1nn) (by rw [harg2eq]; exact harg2nn) hargle

/-- The seam step (`SeamStep`) follows from the `r0` doubling bound. -/
theorem seamStep_of_seamR0 (hr0 : SeamR0Bound) : SeamStep :=
  fun hx1 hx2 hC1 hC01 hC2 hC02 hk hadj =>
    seamStep_of_r0 hr0 hx1 hx2 hC1 hC01 hC2 hC02 hk hadj

end ExpYul
