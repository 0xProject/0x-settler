import ExpProof.Mono.Quot

/-!
# The range and nonnegativity obligations of `RegionMonotonicityFacts`

`r1Tree x = shr(108 − k, WAD·r0 − MARGIN)` closes the kernel: it scales the Q126 quotient onto the
`5¹⁸·2¹⁰⁸` grid, subtracts the one-sided margin, and floors with the `2ᵏ` octave scaling and the
wad unit's remaining `2¹⁸` folded into the shift (`108 − k ∈ [45, 169]`).

* **nonneg**: `r0 ≥ 2^123` gives `WAD·r0 > MARGIN`, and the shift argument is nonnegative; the
  logical shift of a canonical nonnegative word stays nonnegative.
* **range**: `r0 < 2^128` gives `WAD·r0 < 2^170`, so even before the shift the argument is below
  `2^170`, and the floor is below `2^125 < 2^254`.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-! ## The closing shift amount `108 − k` -/

/-- The shift word `evmSub 0x6c k` equals `108 − int256 k` as a `Nat`, and lies in `[45, 169]` on
the meaningful region (`k ∈ [−61, 63]`). -/
theorem closing_shift {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    ∃ s : Nat, evmSub 0x6c (kTree x) = s ∧ 45 ≤ s ∧ s ≤ 169 ∧
      (s : Int) = 108 - int256 (kTree x) := by
  obtain ⟨hklo, hkhi⟩ := kTree_bound hx hC hC0
  have hkw : kTree x < 2 ^ 256 := by unfold kTree; exact evmSar_lt _ _
  -- 108 (as int) - int256 k, transported through evmSub
  have h108 : int256 (0x6c : Nat) = 108 := by
    rw [int256_of_lt (by norm_num)]; simp
  have hip255 : (2:Int)^255 = 57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
    norm_num
  have hsub : int256 (evmSub 0x6c (kTree x)) = 108 - int256 (kTree x) := by
    have := evmSub_transport (a := 0x6c) (b := kTree x) (by norm_num) hkw
      (by rw [h108, hip255]; omega)
      (by rw [h108, hip255]; omega)
    rw [h108] at this; exact this
  -- the result is a small nonnegative word, so its Nat value is 108 - int256 k
  have hsublt : evmSub 0x6c (kTree x) < 2 ^ 256 := evmSub_lt _ _
  have hnn : 0 ≤ int256 (evmSub 0x6c (kTree x)) := by rw [hsub]; omega
  obtain ⟨heq, hlt255⟩ := int256_eq_of_nonneg hsublt hnn
  refine ⟨evmSub 0x6c (kTree x), rfl, ?_, ?_, ?_⟩
  · -- 45 ≤ s
    have : (45 : Int) ≤ ((evmSub 0x6c (kTree x) : Nat) : Int) := by rw [← heq, hsub]; omega
    exact_mod_cast this
  · have : ((evmSub 0x6c (kTree x) : Nat) : Int) ≤ 169 := by rw [← heq, hsub]; omega
    exact_mod_cast this
  · rw [← heq]; exact hsub

/-! ## The shift argument `WAD·r0 − MARGIN` -/

/-- Abstract bound on the shift argument `WAD·r0 − MARGIN` over an opaque `r0` word in
`[2^123, 2^128)`: its signed value is in `[WAD·2^123 − MARGIN, 2^170)`, in particular nonnegative
and below `2^170`. -/
theorem shiftArg_bounds_of {r0 : Nat} (hr0w : r0 < 2 ^ 256)
    (hr0_lo : (2 ^ 123 : Int) ≤ int256 r0) (hr0_hi : int256 r0 < 2 ^ 128) :
    int256 (evmSub (evmMul 0x3782dace9d9 r0) 0x2161b482a02) =
        0x3782dace9d9 * int256 r0 - 0x2161b482a02 ∧
      0 ≤ 0x3782dace9d9 * int256 r0 - 0x2161b482a02 ∧
      0x3782dace9d9 * int256 r0 - 0x2161b482a02 < 2 ^ 170 := by
  have hwad : int256 (0x3782dace9d9 : Nat) = 0x3782dace9d9 := by
    rw [int256_of_lt (by norm_num)]; simp
  have hwadlt : (0x3782dace9d9 : Nat) < 2 ^ 256 := by norm_num
  have hp128 : (2:Int)^128 = 340282366920938463463374607431768211456 := by norm_num
  have hp170 : (2:Int)^170 = 1496577676626844588240573268701473812127674924007424 := by norm_num
  have hwadc : (0x3782dace9d9 : Int) = 3814697265625 := by norm_num
  have hmarc : (0x2161b482a02 : Int) = 2293970250242 := by norm_num
  rw [hp128] at hr0_hi
  -- the product WAD·r0 transported
  have hmul : int256 (evmMul 0x3782dace9d9 r0) = 0x3782dace9d9 * int256 r0 := by
    have := evmMul_transport hwadlt hr0w
      (by rw [hwad, hwadc]; simp only [ipow255]; nlinarith [hr0_lo, hr0_hi])
      (by rw [hwad, hwadc]; simp only [ipow255]; nlinarith [hr0_lo, hr0_hi])
    rw [hwad] at this; exact this
  have hmullt : evmMul 0x3782dace9d9 r0 < 2 ^ 256 := evmMul_lt _ _
  have hmarlt : (0x2161b482a02 : Nat) < 2 ^ 256 := by norm_num
  have hmari : int256 (0x2161b482a02 : Nat) = 0x2161b482a02 := by
    rw [int256_of_lt (by norm_num)]; simp
  -- transport the subtraction
  have hsub : int256 (evmSub (evmMul 0x3782dace9d9 r0) 0x2161b482a02) =
      0x3782dace9d9 * int256 r0 - 0x2161b482a02 := by
    have := evmSub_transport hmullt hmarlt
      (by rw [hmul, hmari, hwadc, hmarc]; simp only [ipow255]; nlinarith [hr0_lo, hr0_hi])
      (by rw [hmul, hmari, hwadc, hmarc]; simp only [ipow255]; nlinarith [hr0_lo, hr0_hi])
    rw [hmul, hmari] at this; exact this
  refine ⟨hsub, ?_, ?_⟩
  · rw [hwadc, hmarc]
    have hp123 : (2:Int)^123 = 10633823966279326983230456482242756608 := by norm_num
    rw [hp123] at hr0_lo
    nlinarith [hr0_lo]
  · rw [hwadc, hmarc, hp170]; nlinarith [hr0_hi]

/-! ## Abstract floor facts for the closing shift -/

/-- Abstract closing-shift facts over an opaque shift argument word `W` and shift `s ∈ [45, 169]`
with `int256 W ∈ [0, 2^170)`: the floor `shr(s, W)` is nonnegative and below `2^125`. -/
theorem closingShr_facts {W s : Nat} (hWw : W < 2 ^ 256) (hslo : 45 ≤ s) (hshi : s ≤ 169)
    (hWnn : 0 ≤ int256 W) (hWhi : int256 W < 2 ^ 170) :
    0 ≤ int256 (evmShr s W) ∧ int256 (evmShr s W) < 2 ^ 125 := by
  obtain ⟨hWi, _⟩ := int256_eq_of_nonneg hWw hWnn
  have hWnat : W < 2 ^ 170 := by
    have : ((W : Nat) : Int) < 2 ^ 170 := by rw [← hWi]; exact hWhi
    exact_mod_cast this
  rw [evmShr_eq_div (by omega) hWw]
  have hqlt : W / 2 ^ s < 2 ^ 125 := by
    have h45 : (2:Nat) ^ 45 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hslo
    have h1 : W / 2 ^ s ≤ W / 2 ^ 45 := Nat.div_le_div_left h45 (Nat.two_pow_pos _)
    have h2 : W / 2 ^ 45 < 2 ^ 125 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      calc W < 2 ^ 170 := hWnat
        _ = 2 ^ 125 * 2 ^ 45 := by rw [← Nat.pow_add]
    omega
  rw [int256_of_lt (by
    have : (2:Nat) ^ 125 < 2 ^ 255 := by norm_num
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
  have hr1 : r1Tree x = evmShr (evmSub 0x6c (kTree x))
      (evmSub (evmMul 0x3782dace9d9 (r0Tree x)) 0x2161b482a02) := rfl
  rw [hr1, hseq]
  exact (closingShr_facts (evmSub_lt _ _) hslo hshi (by rw [hargeq]; exact hargnn)
    (by rw [hargeq]; exact harghi)).1

/-- **`range`**: `r1Tree x < 2^254` on the meaningful region. -/
theorem r1Tree_range {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    r1Tree x < 2 ^ 254 := by
  obtain ⟨s, hseq, hslo, hshi, _⟩ := closing_shift hx hC hC0
  obtain ⟨hr0lo, hr0hi⟩ := r0Tree_bounds hx hC hC0
  obtain ⟨hargeq, hargnn, harghi⟩ := shiftArg_bounds_of (r0 := r0Tree x) (r0Tree_lt x) hr0lo hr0hi
  have hr1 : r1Tree x = evmShr (evmSub 0x6c (kTree x))
      (evmSub (evmMul 0x3782dace9d9 (r0Tree x)) 0x2161b482a02) := rfl
  obtain ⟨hnn, hlt⟩ := closingShr_facts (W := evmSub (evmMul 0x3782dace9d9 (r0Tree x)) 0x2161b482a02)
    (s := s) (evmSub_lt _ _) hslo hshi (by rw [hargeq]; exact hargnn) (by rw [hargeq]; exact harghi)
  -- int256 (r1Tree x) ∈ [0, 2^125) ⇒ the Nat word is < 2^254
  have hReq : int256 (r1Tree x) = int256 (evmShr s (evmSub (evmMul 0x3782dace9d9 (r0Tree x)) 0x2161b482a02)) := by
    rw [hr1, hseq]
  rw [← hReq] at hnn hlt
  have hr1w : r1Tree x < 2 ^ 256 := r1Tree_lt x
  obtain ⟨hi, _⟩ := int256_eq_of_nonneg hr1w hnn
  have hp254 : (2:Int)^125 < 2^254 := by norm_num
  have hcast : ((r1Tree x : Nat) : Int) < 2 ^ 254 := by
    rw [← hi]
    generalize int256 (r1Tree x) = V at hlt ⊢
    omega
  exact_mod_cast hcast

end ExpYul
