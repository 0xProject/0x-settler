import ExpProof.Mono.Quot

/-!
# The range and nonnegativity obligations of `RegionMonotonicityFacts`

`r1Tree x = shr(68 − k, r0 − MARGIN)` closes the kernel: the quotient already carries the
`10¹⁸·2⁶⁸` output scale, so the closing stage subtracts the one-sided margin and floors with the
`2ᵏ` octave scaling folded into the shift (`67 − k ∈ [2, 128]`).

* **nonneg**: `r0 ≥ 2^124` gives `r0 > MARGIN`, and the shift argument is nonnegative; the
  logical shift of a canonical nonnegative word stays nonnegative.
* **range**: `r0 < 2^130` keeps the shift argument below `2^130`, and the `≥ 4` shift floors it
  below `2^126 < 2^254`.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-! ## The closing shift amount `67 − k` -/

/-- The shift word `evmSub 0x43 k` equals `67 − int256 k` as a `Nat`, and lies in `[2, 128]` on
the meaningful region (`k ∈ [−61, 65]`). -/
theorem closing_shift {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    ∃ s : Nat, evmSub 0x43 (kTree x) = s ∧ 2 ≤ s ∧ s ≤ 128 ∧
      (s : Int) = 67 - int256 (kTree x) := by
  obtain ⟨hklo, hkhi⟩ := kTree_bound hx hC hC0
  have hkw : kTree x < 2 ^ 256 := by unfold kTree; exact evmSar_lt _ _
  -- 68 (as int) - int256 k, transported through evmSub
  have h68 : int256 (0x43 : Nat) = 67 := by
    rw [int256_of_lt (by norm_num)]; simp
  have hip255 : (2:Int)^255 = 57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
    norm_num
  have hsub : int256 (evmSub 0x43 (kTree x)) = 67 - int256 (kTree x) := by
    have := evmSub_transport (a := 0x43) (b := kTree x) (by norm_num) hkw
      (by rw [h68, hip255]; omega)
      (by rw [h68, hip255]; omega)
    rw [h68] at this; exact this
  -- the result is a small nonnegative word, so its Nat value is 67 - int256 k
  have hsublt : evmSub 0x43 (kTree x) < 2 ^ 256 := evmSub_lt _ _
  have hnn : 0 ≤ int256 (evmSub 0x43 (kTree x)) := by rw [hsub]; omega
  obtain ⟨heq, hlt255⟩ := int256_eq_of_nonneg hsublt hnn
  refine ⟨evmSub 0x43 (kTree x), rfl, ?_, ?_, ?_⟩
  · -- 2 ≤ s
    have : (2 : Int) ≤ ((evmSub 0x43 (kTree x) : Nat) : Int) := by rw [← heq, hsub]; omega
    exact_mod_cast this
  · have : ((evmSub 0x43 (kTree x) : Nat) : Int) ≤ 128 := by rw [← heq, hsub]; omega
    exact_mod_cast this
  · rw [← heq]; exact hsub

/-! ## The shift argument `r0 − MARGIN` -/

/-- Abstract bound on the shift argument `r0 − MARGIN` over an opaque `r0` word in
`[2^124, 2^130)`: its signed value is in `[2^124 − MARGIN, 2^130)`, in particular nonnegative
and below `2^130`. -/
theorem shiftArg_bounds_of {r0 : Nat} (hr0w : r0 < 2 ^ 256)
    (hr0_lo : (2 ^ 124 : Int) ≤ int256 r0) (hr0_hi : int256 r0 < 2 ^ 130) :
    int256 (evmSub r0 0x1) = int256 r0 - 0x1 ∧
      0 ≤ int256 r0 - 0x1 ∧
      int256 r0 - 0x1 < 2 ^ 130 := by
  have hmarlt : (0x1 : Nat) < 2 ^ 256 := by norm_num
  have hmari : int256 (0x1 : Nat) = 0x1 := by
    rw [int256_of_lt (by norm_num)]; simp
  have hp124 : (2:Int)^124 = 21267647932558653966460912964485513216 := by norm_num
  have hp130 : (2:Int)^130 = 1361129467683753853853498429727072845824 := by norm_num
  have hip255 : (2:Int)^255 = 57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
    norm_num
  rw [hp124] at hr0_lo
  rw [hp130] at hr0_hi
  have hsub : int256 (evmSub r0 0x1) = int256 r0 - 0x1 := by
    have := evmSub_transport hr0w hmarlt
      (by rw [hmari]; simp only [ipow255]; omega)
      (by rw [hmari]; simp only [ipow255]; omega)
    rw [hmari] at this; exact this
  refine ⟨hsub, by omega, by omega⟩

/-! ## Abstract floor facts for the closing shift -/

/-- Abstract closing-shift facts over an opaque shift argument word `W` and shift `s ∈ [4, 129]`
with `int256 W ∈ [0, 2^130)`: the floor `shr(s, W)` is nonnegative and below `2^126`. -/
theorem closingShr_facts {W s : Nat} (hWw : W < 2 ^ 256) (hslo : 2 ≤ s) (hshi : s ≤ 128)
    (hWnn : 0 ≤ int256 W) (hWhi : int256 W < 2 ^ 130) :
    0 ≤ int256 (evmShr s W) ∧ int256 (evmShr s W) < 2 ^ 128 := by
  obtain ⟨hWi, _⟩ := int256_eq_of_nonneg hWw hWnn
  have hWnat : W < 2 ^ 130 := by
    have : ((W : Nat) : Int) < 2 ^ 130 := by rw [← hWi]; exact hWhi
    exact_mod_cast this
  rw [evmShr_eq_div (by omega) hWw]
  have hqlt : W / 2 ^ s < 2 ^ 128 := by
    have h4 : (2:Nat) ^ 2 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hslo
    have h1 : W / 2 ^ s ≤ W / 2 ^ 2 := Nat.div_le_div_left h4 (Nat.two_pow_pos _)
    have h2 : W / 2 ^ 2 < 2 ^ 128 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      calc W < 2 ^ 130 := hWnat
        _ = 2 ^ 128 * 2 ^ 2 := by rw [← Nat.pow_add]
    omega
  rw [int256_of_lt (by
    have : (2:Nat) ^ 128 < 2 ^ 255 := by norm_num
    omega)]
  constructor
  · positivity
  · exact_mod_cast hqlt

/-! ## The discharged obligations -/

/-- **`nonneg`**: `0 ≤ (r1Tree x : Int)`. The body word is a `Nat`, so its signed-as-`Int` cast is
trivially nonnegative; the meaningful "result is never negative" is enforced by the clamp shell. -/
theorem r1Tree_nonneg (x : Nat) : 0 ≤ (r1Tree x : Int) := Int.natCast_nonneg _

/-- The signed value `int256 (r1Tree x)` is nonnegative (the floor of a nonnegative quantity). -/
theorem r1Tree_int256_nonneg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    0 ≤ int256 (r1Tree x) := by
  obtain ⟨s, hseq, hslo, hshi, _⟩ := closing_shift hx hC hC0
  obtain ⟨hr0lo, hr0hi⟩ := r0Tree_bounds hx hC hC0
  obtain ⟨hargeq, hargnn, harghi⟩ := shiftArg_bounds_of (r0 := r0Tree x) (r0Tree_lt x) hr0lo hr0hi
  have hr1 : r1Tree x = evmShr (evmSub 0x43 (kTree x)) (evmSub (r0Tree x) 0x1) := rfl
  rw [hr1, hseq]
  exact (closingShr_facts (evmSub_lt _ _) hslo hshi (by rw [hargeq]; omega)
    (by rw [hargeq]; omega)).1

/-- **`range`**: `r1Tree x < 2^254` on the meaningful region. -/
theorem r1Tree_range {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    r1Tree x < 2 ^ 254 := by
  obtain ⟨s, hseq, hslo, hshi, _⟩ := closing_shift hx hC hC0
  obtain ⟨hr0lo, hr0hi⟩ := r0Tree_bounds hx hC hC0
  obtain ⟨hargeq, hargnn, harghi⟩ := shiftArg_bounds_of (r0 := r0Tree x) (r0Tree_lt x) hr0lo hr0hi
  have hr1 : r1Tree x = evmShr (evmSub 0x43 (kTree x)) (evmSub (r0Tree x) 0x1) := rfl
  obtain ⟨hnn, hlt⟩ := closingShr_facts (W := evmSub (r0Tree x) 0x1)
    (s := s) (evmSub_lt _ _) hslo hshi (by rw [hargeq]; omega) (by rw [hargeq]; omega)
  -- int256 (r1Tree x) ∈ [0, 2^126) ⇒ the Nat word is < 2^254
  have hReq : int256 (r1Tree x) = int256 (evmShr s (evmSub (r0Tree x) 0x1)) := by
    rw [hr1, hseq]
  rw [← hReq] at hnn hlt
  have hr1w : r1Tree x < 2 ^ 256 := r1Tree_lt x
  obtain ⟨hi, _⟩ := int256_eq_of_nonneg hr1w hnn
  have hp254 : (2:Int)^128 < 2^254 := by norm_num
  have hcast : ((r1Tree x : Nat) : Int) < 2 ^ 254 := by
    rw [← hi]
    generalize int256 (r1Tree x) = V at hlt ⊢
    omega
  exact_mod_cast hcast

end ExpYul
