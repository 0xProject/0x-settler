import ExpProof.Mono.Quot

/-!
# The range and nonnegativity obligations of `RegionMonotonicityFacts`

`r1Tree x = sar(126 − k, WAD·r0 − MARGIN)` closes the kernel: it scales the Q126 quotient onto the
`10¹⁸·2¹²⁶` grid, subtracts the one-sided margin, and floors with the `2ᵏ` octave scaling folded
into the shift (`126 − k ∈ [63, 187]`).

* **nonneg**: `r0 ≥ 1` gives `WAD·r0 ≥ WAD > MARGIN`, so the shift argument is nonnegative; a
  nonnegative arithmetic shift stays nonnegative.
* **range**: `r0 < 2^128` gives `WAD·r0 < 2^188`, so even before the shift the argument is below
  `2^188`, and the floor is below `2^125 < 2^254`.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-! ## The closing shift amount `126 − k` -/

/-- The shift word `evmSub 0x7e k` equals `126 − int256 k` as a `Nat`, and lies in `[63, 187]` on
the meaningful region (`k ∈ [−61, 63]`). -/
theorem closing_shift {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    ∃ s : Nat, evmSub 0x7e (kTree x) = s ∧ 63 ≤ s ∧ s ≤ 187 ∧
      (s : Int) = 126 - int256 (kTree x) := by
  obtain ⟨hklo, hkhi⟩ := kTree_bound hx hC hC0
  have hkw : kTree x < 2 ^ 256 := by unfold kTree; exact evmSar_lt _ _
  -- 126 (as int) - int256 k, transported through evmSub
  have h126 : int256 (0x7e : Nat) = 126 := by
    rw [int256_of_lt (by norm_num)]; simp
  have hip255 : (2:Int)^255 = 57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
    norm_num
  have hsub : int256 (evmSub 0x7e (kTree x)) = 126 - int256 (kTree x) := by
    have := evmSub_transport (a := 0x7e) (b := kTree x) (by norm_num) hkw
      (by rw [h126, hip255]; omega)
      (by rw [h126, hip255]; omega)
    rw [h126] at this; exact this
  -- the result is a small nonnegative word, so its Nat value is 126 - int256 k
  have hsublt : evmSub 0x7e (kTree x) < 2 ^ 256 := evmSub_lt _ _
  have hnn : 0 ≤ int256 (evmSub 0x7e (kTree x)) := by rw [hsub]; omega
  obtain ⟨heq, hlt255⟩ := int256_eq_of_nonneg hsublt hnn
  refine ⟨evmSub 0x7e (kTree x), rfl, ?_, ?_, ?_⟩
  · -- 63 ≤ s
    have : (63 : Int) ≤ ((evmSub 0x7e (kTree x) : Nat) : Int) := by rw [← heq, hsub]; omega
    exact_mod_cast this
  · have : ((evmSub 0x7e (kTree x) : Nat) : Int) ≤ 187 := by rw [← heq, hsub]; omega
    exact_mod_cast this
  · rw [← heq]; exact hsub

/-! ## The shift argument `WAD·r0 − MARGIN` -/

/-- Abstract bound on the shift argument `WAD·r0 − MARGIN` over an opaque `r0` word in `[1, 2^128)`:
its signed value is in `[WAD − MARGIN, 2^188)`, in particular nonnegative and below `2^188`. -/
theorem shiftArg_bounds_of {r0 : Nat} (hr0w : r0 < 2 ^ 256)
    (hr0_lo : 1 ≤ int256 r0) (hr0_hi : int256 r0 < 2 ^ 128) :
    int256 (evmSub (evmMul 0xde0b6b3a7640000 r0) 0x9fe769d0fa58e9f) =
        0xde0b6b3a7640000 * int256 r0 - 0x9fe769d0fa58e9f ∧
      0 ≤ 0xde0b6b3a7640000 * int256 r0 - 0x9fe769d0fa58e9f ∧
      0xde0b6b3a7640000 * int256 r0 - 0x9fe769d0fa58e9f < 2 ^ 188 := by
  have hwad : int256 (0xde0b6b3a7640000 : Nat) = 0xde0b6b3a7640000 := by
    rw [int256_of_lt (by norm_num)]; simp
  have hwadlt : (0xde0b6b3a7640000 : Nat) < 2 ^ 256 := by norm_num
  have hp128 : (2:Int)^128 = 340282366920938463463374607431768211456 := by norm_num
  have hp188 : (2:Int)^188 = 392318858461667547739736838950479151006397215279002157056 := by norm_num
  have hwadc : (0xde0b6b3a7640000 : Int) = 1000000000000000000 := by norm_num
  have hmarc : (0x9fe769d0fa58e9f : Int) = 720143407370309279 := by norm_num
  rw [hp128] at hr0_hi
  -- the product WAD·r0 transported
  have hmul : int256 (evmMul 0xde0b6b3a7640000 r0) = 0xde0b6b3a7640000 * int256 r0 := by
    have := evmMul_transport hwadlt hr0w
      (by rw [hwad, hwadc]; simp only [ipow255]; nlinarith [hr0_lo, hr0_hi])
      (by rw [hwad, hwadc]; simp only [ipow255]; nlinarith [hr0_lo, hr0_hi])
    rw [hwad] at this; exact this
  have hmullt : evmMul 0xde0b6b3a7640000 r0 < 2 ^ 256 := evmMul_lt _ _
  have hmarlt : (0x9fe769d0fa58e9f : Nat) < 2 ^ 256 := by norm_num
  have hmari : int256 (0x9fe769d0fa58e9f : Nat) = 0x9fe769d0fa58e9f := by
    rw [int256_of_lt (by norm_num)]; simp
  -- transport the subtraction
  have hsub : int256 (evmSub (evmMul 0xde0b6b3a7640000 r0) 0x9fe769d0fa58e9f) =
      0xde0b6b3a7640000 * int256 r0 - 0x9fe769d0fa58e9f := by
    have := evmSub_transport hmullt hmarlt
      (by rw [hmul, hmari, hwadc, hmarc]; simp only [ipow255]; nlinarith [hr0_lo, hr0_hi])
      (by rw [hmul, hmari, hwadc, hmarc]; simp only [ipow255]; nlinarith [hr0_lo, hr0_hi])
    rw [hmul, hmari] at this; exact this
  refine ⟨hsub, ?_, ?_⟩
  · rw [hwadc, hmarc]; nlinarith [hr0_lo]
  · rw [hwadc, hmarc, hp188]; nlinarith [hr0_hi]

/-! ## Abstract floor facts for the closing shift -/

/-- Abstract closing-shift facts over an opaque shift argument word `W` and shift `s ∈ [63, 187]`
with `int256 W ∈ [0, 2^188)`: the floor `sar(s, W)` is nonnegative and below `2^125`. -/
theorem closingSar_facts {W s : Nat} (hWw : W < 2 ^ 256) (hslo : 63 ≤ s) (hshi : s ≤ 187)
    (hWnn : 0 ≤ int256 W) (hWhi : int256 W < 2 ^ 188) :
    0 ≤ int256 (evmSar s W) ∧ int256 (evmSar s W) < 2 ^ 125 := by
  obtain ⟨_, hsl, hsh⟩ := evmSar_sandwich (s := s) (by omega) hWw
  have hpow : (0 : Int) < 2 ^ s := by positivity
  set R := int256 (evmSar s W) with hR
  have hnn : 0 ≤ R := by
    by_contra hneg
    push_neg at hneg
    have h2 : (2 : Int) ^ s * (R + 1) ≤ 0 := by
      have : (2:Int)^s * (R + 1) ≤ 2^s * 0 := mul_le_mul_left_nonneg (by omega) (le_of_lt hpow)
      simpa using this
    nlinarith [hWnn, h2, hsh]
  refine ⟨hnn, ?_⟩
  have hp63 : (2 : Int) ^ 63 ≤ 2 ^ s := pow_le_pow_right₀ (by norm_num) hslo
  by_contra hge
  push_neg at hge
  have hp188 : (2:Int)^188 = 392318858461667547739736838950479151006397215279002157056 := by norm_num
  have hp125 : (2:Int)^125 = 42535295865117307932921825928971026432 := by norm_num
  have hp63v : (2:Int)^63 = 9223372036854775808 := by norm_num
  have h1 : (2:Int)^63 * 2^125 ≤ 2^63 * R := mul_le_mul_left_nonneg hge (by positivity)
  have h2 : (2:Int)^63 * R ≤ 2^s * R := mul_le_mul_right_nonneg hp63 hnn
  rw [hp188] at hWhi
  rw [hp63v, hp125] at h1
  nlinarith [hsl, hWhi, h1, h2]

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
  have hr1 : r1Tree x = evmSar (evmSub 0x7e (kTree x))
      (evmSub (evmMul 0xde0b6b3a7640000 (r0Tree x)) 0x9fe769d0fa58e9f) := rfl
  rw [hr1, hseq]
  exact (closingSar_facts (evmSub_lt _ _) hslo hshi (by rw [hargeq]; exact hargnn)
    (by rw [hargeq]; exact harghi)).1

/-- **`range`**: `r1Tree x < 2^254` on the meaningful region. -/
theorem r1Tree_range {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    r1Tree x < 2 ^ 254 := by
  obtain ⟨s, hseq, hslo, hshi, _⟩ := closing_shift hx hC hC0
  obtain ⟨hr0lo, hr0hi⟩ := r0Tree_bounds hx hC hC0
  obtain ⟨hargeq, hargnn, harghi⟩ := shiftArg_bounds_of (r0 := r0Tree x) (r0Tree_lt x) hr0lo hr0hi
  have hr1 : r1Tree x = evmSar (evmSub 0x7e (kTree x))
      (evmSub (evmMul 0xde0b6b3a7640000 (r0Tree x)) 0x9fe769d0fa58e9f) := rfl
  obtain ⟨hnn, hlt⟩ := closingSar_facts (W := evmSub (evmMul 0xde0b6b3a7640000 (r0Tree x)) 0x9fe769d0fa58e9f)
    (s := s) (evmSub_lt _ _) hslo hshi (by rw [hargeq]; exact hargnn) (by rw [hargeq]; exact harghi)
  -- int256 (r1Tree x) ∈ [0, 2^125) ⇒ the Nat word is < 2^254
  have hReq : int256 (r1Tree x) = int256 (evmSar s (evmSub (evmMul 0xde0b6b3a7640000 (r0Tree x)) 0x9fe769d0fa58e9f)) := by
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
