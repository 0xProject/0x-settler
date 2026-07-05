import ExpProof.Mono.CrossCert
import ExpProof.Mono.RangeNonneg

/-!
# The within-octave adjacent step

For two inputs adjacent in the signed order (`int256 x2 = int256 x1 + 1`) in a common octave, the
quotient `r0` is nondecreasing (`r0_mono_adjacent`, via the cross inequality `tod_cross` fed to
`r0_mono_of_cross`), and hence so is the closing accumulator `r1` (`r1_mono_adjacent`): with `k`
fixed the closing shift `67 − k` is fixed, and the logical-shift floor of the nondecreasing
`r0 − MARGIN` is nondecreasing.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-- The `tod`-bound hypotheses of `r0_mono_of_cross`, in the `2^126` form. -/
theorem todTree_cross_bounds {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    -(85070591730234615865843651857942052864 : Int) ≤ int256 (todTree x) ∧
      int256 (todTree x) < 85070591730234615865843651857942052864 := by
  obtain ⟨hlo, hhi, _, _⟩ := todTree_bound hx hC hC0
  refine ⟨?_, ?_⟩
  · rw [show (85070591730234615865843651857942052864 : Int) = 2 ^ 126 by norm_num]; exact hlo
  · rw [show (85070591730234615865843651857942052864 : Int) = 2 ^ 126 by norm_num]; exact hhi

/-- **Adjacent `r0` monotonicity** within an octave. -/
theorem r0_mono_adjacent {x1 x2 : Nat} (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hC1 : int256 Cmask < int256 x1) (hC01 : int256 x1 < int256 C0thresh)
    (hC2 : int256 Cmask < int256 x2) (hC02 : int256 x2 < int256 C0thresh)
    (hk : int256 (kTree x1) = int256 (kTree x2))
    (hadj : int256 x2 = int256 x1 + 1) :
    int256 (r0Tree x1) ≤ int256 (r0Tree x2) := by
  have hv1 : vTree x1 < 2 ^ 120 := (vTree_eq hx1 hC1 hC01).2
  have hv2 : vTree x2 < 2 ^ 120 := (vTree_eq hx2 hC2 hC02).2
  obtain ⟨hev1lo, hev1hi⟩ := evTree_int hv1
  obtain ⟨hev2lo, hev2hi⟩ := evTree_int hv2
  obtain ⟨htod1lo, htod1hi⟩ := todTree_cross_bounds hx1 hC1 hC01
  obtain ⟨htod2lo, htod2hi⟩ := todTree_cross_bounds hx2 hC2 hC02
  have hevw1 : evTree x1 < 2 ^ 256 := by unfold evTree; exact evmAdd_lt _ _
  have hevw2 : evTree x2 < 2 ^ 256 := by unfold evTree; exact evmAdd_lt _ _
  have htodw1 : todTree x1 < 2 ^ 256 := by unfold todTree; exact evmSar_lt _ _
  have htodw2 : todTree x2 < 2 ^ 256 := by unfold todTree; exact evmSar_lt _ _
  have hcross := tod_cross hx1 hx2 hC1 hC01 hC2 hC02 hk hadj
  have hr01 : r0Tree x1 =
      evmDiv (evmMul scaleQ67 (evmAdd (evTree x1) (todTree x1))) (evmSub (evTree x1) (todTree x1)) := rfl
  have hr02 : r0Tree x2 =
      evmDiv (evmMul scaleQ67 (evmAdd (evTree x2) (todTree x2))) (evmSub (evTree x2) (todTree x2)) := rfl
  rw [hr01, hr02]
  exact r0_mono_of_cross hevw1 htodw1 hevw2 htodw2 hev1lo hev1hi htod1lo htod1hi
    hev2lo hev2hi htod2lo htod2hi hcross

/-- The closing shift words coincide across an octave. -/
theorem closing_shift_eq {x1 x2 : Nat}
    (hk : int256 (kTree x1) = int256 (kTree x2))
    (hk1 : kTree x1 < 2 ^ 256) (hk2 : kTree x2 < 2 ^ 256) :
    evmSub 0x43 (kTree x1) = evmSub 0x43 (kTree x2) := by
  -- `int256` is injective on canonical words (`[0, 2^256)`), so `k` words coincide.
  have hinj : ∀ a b : Nat, a < 2 ^ 256 → b < 2 ^ 256 → int256 a = int256 b → a = b := by
    intro a b ha hb h
    have hp : (2 : Int) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
      intPow256
    have ha' : (a : Int) < 2 ^ 256 := by exact_mod_cast ha
    have hb' : (b : Int) < 2 ^ 256 := by exact_mod_cast hb
    rw [hp] at ha' hb'
    unfold int256 at h
    split at h <;> split at h <;> first | (rw [hp] at h; omega) | omega
  rw [hinj _ _ hk1 hk2 hk]

/-- **Adjacent `r1` monotonicity** within an octave: with `k` fixed, the closing shift is fixed and
the logical-shift floor of the nondecreasing shift argument is nondecreasing. -/
theorem r1_mono_adjacent {x1 x2 : Nat} (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hC1 : int256 Cmask < int256 x1) (hC01 : int256 x1 < int256 C0thresh)
    (hC2 : int256 Cmask < int256 x2) (hC02 : int256 x2 < int256 C0thresh)
    (hk : int256 (kTree x1) = int256 (kTree x2))
    (hadj : int256 x2 = int256 x1 + 1) :
    int256 (r1Tree x1) ≤ int256 (r1Tree x2) := by
  have hr0mono := r0_mono_adjacent hx1 hx2 hC1 hC01 hC2 hC02 hk hadj
  obtain ⟨hr0lo1, hr0hi1⟩ := r0Tree_bounds hx1 hC1 hC01
  obtain ⟨hr0lo2, hr0hi2⟩ := r0Tree_bounds hx2 hC2 hC02
  -- the shift argument `r0 − MARGIN` is nondecreasing
  obtain ⟨harg1eq, harg1nn, harg1hi⟩ := shiftArg_bounds_of (r0 := r0Tree x1) (r0Tree_lt x1) hr0lo1 hr0hi1
  obtain ⟨harg2eq, harg2nn, harg2hi⟩ := shiftArg_bounds_of (r0 := r0Tree x2) (r0Tree_lt x2) hr0lo2 hr0hi2
  -- the closing shift words coincide
  have hk1w : kTree x1 < 2 ^ 256 := by unfold kTree; exact evmSar_lt _ _
  have hk2w : kTree x2 < 2 ^ 256 := by unfold kTree; exact evmSar_lt _ _
  have hseq := closing_shift_eq hk hk1w hk2w
  obtain ⟨s, hseqx, hslo, hshi, _⟩ := closing_shift hx1 hC1 hC01
  have hr1eq1 : r1Tree x1 = evmShr s (evmSub (r0Tree x1) 0x1) := by
    unfold r1Tree; rw [hseqx]
  have hr1eq2 : r1Tree x2 = evmShr s (evmSub (r0Tree x2) 0x1) := by
    unfold r1Tree; rw [← hseq, hseqx]
  rw [hr1eq1, hr1eq2]
  -- the two shift arguments, transported to `Int`, are ordered (monotone `r0`)
  set arg1 := evmSub (r0Tree x1) 0x1 with harg1
  set arg2 := evmSub (r0Tree x2) 0x1 with harg2
  have ha1lt : arg1 < 2 ^ 256 := by rw [harg1]; exact evmSub_lt _ _
  have ha2lt : arg2 < 2 ^ 256 := by rw [harg2]; exact evmSub_lt _ _
  -- the deep tree behind the shift arguments is opaque from here on
  clear_value arg1 arg2
  have hargle : int256 arg1 ≤ int256 arg2 := by
    rw [harg1eq, harg2eq]
    exact sub_le_sub_right hr0mono 0x1
  -- the shift arguments are nonnegative canonical words, ordered as Nats
  obtain ⟨he1, hlt1⟩ := int256_eq_of_nonneg ha1lt (by rw [harg1eq]; exact harg1nn)
  obtain ⟨he2, hlt2⟩ := int256_eq_of_nonneg ha2lt (by rw [harg2eq]; exact harg2nn)
  have hargleN : arg1 ≤ arg2 := by
    have : ((arg1 : Nat) : Int) ≤ ((arg2 : Nat) : Int) := by rw [← he1, ← he2]; exact hargle
    exact_mod_cast this
  -- `evmShr s` is the same-shift Nat floor: monotone
  rw [evmShr_eq_div (by omega) ha1lt, evmShr_eq_div (by omega) ha2lt]
  have hqle : arg1 / 2 ^ s ≤ arg2 / 2 ^ s := Nat.div_le_div_right hargleN
  have hq1lt : arg1 / 2 ^ s < 2 ^ 255 := by
    have h1 : arg1 / 2 ^ s ≤ arg1 := Nat.div_le_self _ _
    omega
  have hq2lt : arg2 / 2 ^ s < 2 ^ 255 := by
    have h1 : arg2 / 2 ^ s ≤ arg2 := Nat.div_le_self _ _
    omega
  rw [int256_of_lt hq1lt, int256_of_lt hq2lt]
  exact_mod_cast hqle

end ExpYul
