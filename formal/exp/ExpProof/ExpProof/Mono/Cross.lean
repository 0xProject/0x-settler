import ExpProof.Mono.Quot

/-!
# Same-octave monotonicity of the quotient `r0`

Within a fixed octave (`k` constant) the closing accumulator `r1Tree` is monotone in the input iff
the scaled quotient `r0Tree` is. With `num = ev + tod`, `den = ev − tod` (both strictly positive),
`r0 = ⌊scaleQ68·num/den⌋`, so

```
r0(x1) ≤ r0(x2)  ⟸  num1·den2 ≤ num2·den1    (cross-multiply over positive den)
```

and the cross product simplifies exactly:

```
num1·den2 − num2·den1 = 2·(tod1·ev2 − tod2·ev1),
```

so the whole same-octave step reduces to `tod1·ev2 ≤ tod2·ev1`. This file proves that reduction (the
algebraic identity and the cross-to-division transport); the inequality `tod1·ev2 ≤ tod2·ev1` itself
is the same-octave analytic certificate (it holds with large slack at the guaranteed per-step
reduced-argument gap, and fails only at sub-step granularity).
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-- The cross-product of the two reciprocal-symmetric fractions collapses to a `tod·ev` cross. -/
theorem cross_identity (ev1 ev2 tod1 tod2 : Int) :
    (ev1 + tod1) * (ev2 - tod2) - (ev2 + tod2) * (ev1 - tod1) =
      2 * (tod1 * ev2 - tod2 * ev1) := by ring

/-- `num = ev + tod < 2^128` (signed), from the even-accumulator and reduced-argument bounds. Stated
as its own lemma so it carries a fresh kernel stack frame. -/
theorem numSum_lt {W : Nat} {ev tod : Int} (hW : int256 W = ev + tod)
    (hev : ev < 3 * 2 ^ 126) (htod : tod < 2 ^ 126) : int256 W < 2 ^ 128 := by
  rw [hW, show (2:Int)^128 = 3 * 2^126 + 2^126 from by ring]; omega

/-- The `mul scaleQ68 N` dividend as a plain `Nat` product when `N`'s signed value is in
`[0, 2^128)`: `evmMul scaleQ68 N = scaleQ68 * N` (no wrap), and `N` is its own signed value. -/
theorem mulScale_transport {N : Nat} (hNw : N < 2 ^ 256) (hNnn : 0 ≤ int256 N)
    (hNlt : int256 N < 2 ^ 128) :
    evmMul scaleQ68 N = scaleQ68 * N ∧ N < 2 ^ 128 := by
  obtain ⟨hNi, _⟩ := int256_eq_of_nonneg hNw hNnn
  have hNnat : N < 2 ^ 128 := by
    have : ((N : Nat) : Int) < 2 ^ 128 := by rw [← hNi]; exact hNlt
    exact_mod_cast this
  have hsw : scaleQ68 < 2 ^ 256 := by unfold scaleQ68; norm_num
  have hfit : scaleQ68 * N < 2 ^ 256 := by
    have h1 : scaleQ68 * N ≤ scaleQ68 * 2 ^ 128 := Nat.mul_le_mul_left _ (le_of_lt hNnat)
    have h2 : scaleQ68 * 2 ^ 128 < 2 ^ 256 := by unfold scaleQ68; norm_num
    omega
  exact ⟨evmMul_eq_nat hsw hNw hfit, hNnat⟩

/-- Abstract `r0` monotonicity from the `tod·ev` cross inequality, over opaque even/odd words.
Given the numerator/denominator positivity and `tod1·ev2 ≤ tod2·ev1`, the two `div` quotients are
`≤`-ordered. -/
theorem r0_mono_of_cross {E1 TD1 E2 TD2 : Nat}
    (hE1 : E1 < 2 ^ 256) (hTD1 : TD1 < 2 ^ 256) (hE2 : E2 < 2 ^ 256) (hTD2 : TD2 < 2 ^ 256)
    (hev1_lo : (207573926795459379279817565122117813128 : Int) ≤ (E1 : Int))
    (hev1_hi : (E1 : Int) < 3 * 2 ^ 126)
    (htod1_lo : -(85070591730234615865843651857942052864 : Int) ≤ int256 TD1)
    (htod1_hi : int256 TD1 < 85070591730234615865843651857942052864)
    (hev2_lo : (207573926795459379279817565122117813128 : Int) ≤ (E2 : Int))
    (hev2_hi : (E2 : Int) < 3 * 2 ^ 126)
    (htod2_lo : -(85070591730234615865843651857942052864 : Int) ≤ int256 TD2)
    (htod2_hi : int256 TD2 < 85070591730234615865843651857942052864)
    (hcross : int256 TD1 * (E2 : Int) ≤ int256 TD2 * (E1 : Int)) :
    int256 (evmDiv (evmMul scaleQ68 (evmAdd E1 TD1)) (evmSub E1 TD1)) ≤
      int256 (evmDiv (evmMul scaleQ68 (evmAdd E2 TD2)) (evmSub E2 TD2)) := by
  obtain ⟨hadd1, hsub1, hnum1, hden1⟩ := numden_pos_of hE1 hTD1 hev1_lo hev1_hi htod1_lo htod1_hi
  obtain ⟨hadd2, hsub2, hnum2, hden2⟩ := numden_pos_of hE2 hTD2 hev2_lo hev2_hi htod2_lo htod2_hi
  -- the tod magnitude in the symbolic power form
  have htod1_hi' : int256 TD1 < 2 ^ 126 := by
    have : (85070591730234615865843651857942052864 : Int) = 2 ^ 126 := by norm_num
    omega
  have htod2_hi' : int256 TD2 < 2 ^ 126 := by
    have : (85070591730234615865843651857942052864 : Int) = 2 ^ 126 := by norm_num
    omega
  -- numerator/denominator are positive and below 2^128 (signed)
  have hN1lt : int256 (evmAdd E1 TD1) < 2 ^ 128 := numSum_lt hadd1 hev1_hi htod1_hi'
  have hN2lt : int256 (evmAdd E2 TD2) < 2 ^ 128 := numSum_lt hadd2 hev2_hi htod2_hi'
  -- denominator positivity in `int256 (evmSub …)` form
  have hD1pos : 0 < int256 (evmSub E1 TD1) := by rw [hsub1]; exact hden1
  have hD2pos : 0 < int256 (evmSub E2 TD2) := by rw [hsub2]; exact hden2
  -- mul dividends as plain Nat products
  obtain ⟨hA1, hN1nat⟩ := mulScale_transport (evmAdd_lt _ _) (le_of_lt (hadd1 ▸ hnum1)) hN1lt
  obtain ⟨hA2, hN2nat⟩ := mulScale_transport (evmAdd_lt _ _) (le_of_lt (hadd2 ▸ hnum2)) hN2lt
  -- canonical Nat values for the numerators and denominators
  obtain ⟨hN1i, _⟩ := int256_eq_of_nonneg (evmAdd_lt E1 TD1) (le_of_lt (hadd1 ▸ hnum1))
  obtain ⟨hN2i, _⟩ := int256_eq_of_nonneg (evmAdd_lt E2 TD2) (le_of_lt (hadd2 ▸ hnum2))
  obtain ⟨hD1i, _⟩ := int256_eq_of_nonneg (evmSub_lt E1 TD1) (le_of_lt hD1pos)
  obtain ⟨hD2i, _⟩ := int256_eq_of_nonneg (evmSub_lt E2 TD2) (le_of_lt hD2pos)
  have hD1posN : 0 < evmSub E1 TD1 := by
    have h : (0:Int) < ((evmSub E1 TD1 : Nat) : Int) := by rw [← hD1i]; exact hD1pos
    exact_mod_cast h
  have hD2posN : 0 < evmSub E2 TD2 := by
    have h : (0:Int) < ((evmSub E2 TD2 : Nat) : Int) := by rw [← hD2i]; exact hD2pos
    exact_mod_cast h
  have hD1nz : evmSub E1 TD1 ≠ 0 := Nat.pos_iff_ne_zero.mp hD1posN
  have hD2nz : evmSub E2 TD2 ≠ 0 := Nat.pos_iff_ne_zero.mp hD2posN
  have hsw : scaleQ68 < 2 ^ 256 := by unfold scaleQ68; norm_num
  have hfit1 : scaleQ68 * evmAdd E1 TD1 < 2 ^ 256 := by
    have h1 : scaleQ68 * evmAdd E1 TD1 ≤ scaleQ68 * 2 ^ 128 :=
      Nat.mul_le_mul_left _ (le_of_lt hN1nat)
    have h2 : scaleQ68 * 2 ^ 128 < 2 ^ 256 := by unfold scaleQ68; norm_num
    omega
  have hfit2 : scaleQ68 * evmAdd E2 TD2 < 2 ^ 256 := by
    have h1 : scaleQ68 * evmAdd E2 TD2 ≤ scaleQ68 * 2 ^ 128 :=
      Nat.mul_le_mul_left _ (le_of_lt hN2nat)
    have h2 : scaleQ68 * 2 ^ 128 < 2 ^ 256 := by unfold scaleQ68; norm_num
    omega
  -- the two quotients as plain Nat floor divisions
  have hq1 : evmDiv (evmMul scaleQ68 (evmAdd E1 TD1)) (evmSub E1 TD1) =
      scaleQ68 * evmAdd E1 TD1 / evmSub E1 TD1 := by
    rw [hA1, evmDiv_eq hfit1 (evmSub_lt _ _) hD1nz]
  have hq2 : evmDiv (evmMul scaleQ68 (evmAdd E2 TD2)) (evmSub E2 TD2) =
      scaleQ68 * evmAdd E2 TD2 / evmSub E2 TD2 := by
    rw [hA2, evmDiv_eq hfit2 (evmSub_lt _ _) hD2nz]
  -- Nat-level cross monotonicity: q1·D1 ≤ S·N1, S·N1·D2 ≤ S·N2·D1 ⇒ q1·D2 ≤ S·N2 ⇒ q1 ≤ q2
  have hcrossN : evmAdd E1 TD1 * evmSub E2 TD2 ≤ evmAdd E2 TD2 * evmSub E1 TD1 := by
    have hInt : ((evmAdd E1 TD1 : Nat) : Int) * ((evmSub E2 TD2 : Nat) : Int) ≤
        ((evmAdd E2 TD2 : Nat) : Int) * ((evmSub E1 TD1 : Nat) : Int) := by
      rw [← hN1i, ← hN2i, ← hD1i, ← hD2i, hadd1, hadd2, hsub1, hsub2]
      have hid1 := cross_identity (E1 : Int) (E2 : Int) (int256 TD1) (int256 TD2)
      nlinarith [hcross, hid1]
    exact_mod_cast hInt
  have hD1pos' : 0 < evmSub E1 TD1 := Nat.pos_of_ne_zero hD1nz
  have hD2pos' : 0 < evmSub E2 TD2 := Nat.pos_of_ne_zero hD2nz
  have hqle : scaleQ68 * evmAdd E1 TD1 / evmSub E1 TD1 ≤
      scaleQ68 * evmAdd E2 TD2 / evmSub E2 TD2 := by
    rw [Nat.le_div_iff_mul_le hD2pos']
    have hfl : scaleQ68 * evmAdd E1 TD1 / evmSub E1 TD1 * evmSub E1 TD1 ≤
        scaleQ68 * evmAdd E1 TD1 := Nat.div_mul_le_self _ _
    -- (q1·D2)·D1 ≤ S·N1·D2 ≤ S·N2·D1 ⇒ q1·D2 ≤ S·N2 (divide by D1 > 0)
    have hstep : scaleQ68 * evmAdd E1 TD1 / evmSub E1 TD1 * evmSub E2 TD2 * evmSub E1 TD1 ≤
        scaleQ68 * evmAdd E2 TD2 * evmSub E1 TD1 := by
      calc scaleQ68 * evmAdd E1 TD1 / evmSub E1 TD1 * evmSub E2 TD2 * evmSub E1 TD1
          = scaleQ68 * evmAdd E1 TD1 / evmSub E1 TD1 * evmSub E1 TD1 * evmSub E2 TD2 := by ring
        _ ≤ scaleQ68 * evmAdd E1 TD1 * evmSub E2 TD2 := Nat.mul_le_mul_right _ hfl
        _ = scaleQ68 * (evmAdd E1 TD1 * evmSub E2 TD2) := by ring
        _ ≤ scaleQ68 * (evmAdd E2 TD2 * evmSub E1 TD1) := Nat.mul_le_mul_left _ hcrossN
        _ = scaleQ68 * evmAdd E2 TD2 * evmSub E1 TD1 := by ring
    exact Nat.le_of_mul_le_mul_right hstep hD1pos'
  -- transport back to int256 (both quotients are small: den ≥ 2^126)
  have hD1ge : 2 ^ 126 ≤ evmSub E1 TD1 := by
    have h : (85070591730234615865843651857942052864 : Int) ≤ ((evmSub E1 TD1 : Nat) : Int) := by
      rw [← hD1i, hsub1]
      linarith [hev1_lo, htod1_hi]
    exact_mod_cast h
  have hD2ge : 2 ^ 126 ≤ evmSub E2 TD2 := by
    have h : (85070591730234615865843651857942052864 : Int) ≤ ((evmSub E2 TD2 : Nat) : Int) := by
      rw [← hD2i, hsub2]
      linarith [hev2_lo, htod2_hi]
    exact_mod_cast h
  have hq1small : scaleQ68 * evmAdd E1 TD1 / evmSub E1 TD1 < 2 ^ 255 := by
    have h1 : scaleQ68 * evmAdd E1 TD1 / evmSub E1 TD1 ≤ scaleQ68 * evmAdd E1 TD1 / 2 ^ 126 :=
      Nat.div_le_div_left hD1ge (Nat.two_pow_pos _)
    have h2 : scaleQ68 * evmAdd E1 TD1 / 2 ^ 126 < 2 ^ 130 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      calc scaleQ68 * evmAdd E1 TD1 < 2 ^ 256 := hfit1
        _ = 2 ^ 130 * 2 ^ 126 := by norm_num
    have h3 : (2:Nat) ^ 130 < 2 ^ 255 := by norm_num
    omega
  have hq2small : scaleQ68 * evmAdd E2 TD2 / evmSub E2 TD2 < 2 ^ 255 := by
    have h1 : scaleQ68 * evmAdd E2 TD2 / evmSub E2 TD2 ≤ scaleQ68 * evmAdd E2 TD2 / 2 ^ 126 :=
      Nat.div_le_div_left hD2ge (Nat.two_pow_pos _)
    have h2 : scaleQ68 * evmAdd E2 TD2 / 2 ^ 126 < 2 ^ 130 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      calc scaleQ68 * evmAdd E2 TD2 < 2 ^ 256 := hfit2
        _ = 2 ^ 130 * 2 ^ 126 := by norm_num
    have h3 : (2:Nat) ^ 130 < 2 ^ 255 := by norm_num
    omega
  rw [hq1, hq2, int256_of_lt hq1small, int256_of_lt hq2small]
  exact_mod_cast hqle

end ExpYul
