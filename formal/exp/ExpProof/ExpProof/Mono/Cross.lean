import ExpProof.Mono.Quot

/-!
# Same-octave monotonicity of the quotient `r0`

Within a fixed octave (`k` constant) the closing accumulator `r1Tree` is monotone in the input iff
the Q126 quotient `r0Tree` is. With `num = ev + tod`, `den = ev − tod` (both strictly positive),
`r0 = ⌊2^126·num/den⌋`, so

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
    (hev : ev < 2 ^ 127) (htod : tod < 2 ^ 127) : int256 W < 2 ^ 128 := by
  rw [hW, show (2:Int)^128 = 2^127 + 2^127 from by ring]; omega

/-- The `shl 0x7e N` dividend transported to `Int` when `N`'s signed value is in `[0, 2^128)`:
`int256 (shl 126 N) = 2^126 · int256 N`, and the result is in `[0, 2^255)`. -/
theorem shl126_transport {N : Nat} (hNw : N < 2 ^ 256) (hNnn : 0 ≤ int256 N)
    (hNlt : int256 N < 2 ^ 128) :
    int256 (evmShl 0x7e N) = 2 ^ 0x7e * int256 N := by
  obtain ⟨hNi, _⟩ := int256_eq_of_nonneg hNw hNnn
  have hNnat : N < 2 ^ 128 := by
    have : ((N : Nat) : Int) < 2 ^ 128 := by rw [← hNi]; exact hNlt
    exact_mod_cast this
  have hfit : N * 2 ^ 0x7e < 2 ^ 256 := by
    calc N * 2 ^ 0x7e < 2 ^ 128 * 2 ^ 0x7e := (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hNnat
      _ = 2 ^ 254 := by rw [← Nat.pow_add]
      _ < 2 ^ 256 := by norm_num
  have hfit255 : N * 2 ^ 0x7e < 2 ^ 255 := by
    calc N * 2 ^ 0x7e < 2 ^ 128 * 2 ^ 0x7e := (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hNnat
      _ = 2 ^ 254 := by rw [← Nat.pow_add]
      _ < 2 ^ 255 := by norm_num
  rw [evmShl_eq (by norm_num) hfit, int256_of_lt hfit255, hNi]
  push_cast; ring

/-- Abstract `r0` monotonicity from the `tod·ev` cross inequality, over opaque even/odd words.
Given the numerator/denominator positivity and `tod1·ev2 ≤ tod2·ev1`, the two `sdiv` quotients are
`≤`-ordered. -/
theorem r0_mono_of_cross {E1 TD1 E2 TD2 : Nat}
    (hE1 : E1 < 2 ^ 256) (hTD1 : TD1 < 2 ^ 256) (hE2 : E2 < 2 ^ 256) (hTD2 : TD2 < 2 ^ 256)
    (hev1_lo : (103786963397729689639908782561058906594 : Int) ≤ (E1 : Int))
    (hev1_hi : (E1 : Int) < 2 ^ 127)
    (htod1_lo : -(42535295865117307932921825928971026432 : Int) ≤ int256 TD1)
    (htod1_hi : int256 TD1 < 42535295865117307932921825928971026432)
    (hev2_lo : (103786963397729689639908782561058906594 : Int) ≤ (E2 : Int))
    (hev2_hi : (E2 : Int) < 2 ^ 127)
    (htod2_lo : -(42535295865117307932921825928971026432 : Int) ≤ int256 TD2)
    (htod2_hi : int256 TD2 < 42535295865117307932921825928971026432)
    (hcross : int256 TD1 * (E2 : Int) ≤ int256 TD2 * (E1 : Int)) :
    int256 (evmSdiv (evmShl 0x7e (evmAdd E1 TD1)) (evmSub E1 TD1)) ≤
      int256 (evmSdiv (evmShl 0x7e (evmAdd E2 TD2)) (evmSub E2 TD2)) := by
  obtain ⟨hadd1, hsub1, hnum1, hden1⟩ := numden_pos_of hE1 hTD1 hev1_lo hev1_hi htod1_lo htod1_hi
  obtain ⟨hadd2, hsub2, hnum2, hden2⟩ := numden_pos_of hE2 hTD2 hev2_lo hev2_hi htod2_lo htod2_hi
  -- bound the tod magnitude by 2^127 (looser, symbolic) to avoid large-literal kernel work
  have htod1_hi' : int256 TD1 < 2 ^ 127 := by
    have : (42535295865117307932921825928971026432 : Int) < 2 ^ 127 := by norm_num
    omega
  have htod2_hi' : int256 TD2 < 2 ^ 127 := by
    have : (42535295865117307932921825928971026432 : Int) < 2 ^ 127 := by norm_num
    omega
  -- numerator/denominator are positive and below 2^128 (signed)
  have hN1lt : int256 (evmAdd E1 TD1) < 2 ^ 128 := numSum_lt hadd1 hev1_hi htod1_hi'
  have hN2lt : int256 (evmAdd E2 TD2) < 2 ^ 128 := numSum_lt hadd2 hev2_hi htod2_hi'
  -- denominator positivity in `int256 (evmSub …)` form
  have hD1pos : 0 < int256 (evmSub E1 TD1) := by rw [hsub1]; exact hden1
  have hD2pos : 0 < int256 (evmSub E2 TD2) := by rw [hsub2]; exact hden2
  -- shl dividends transported
  have hA1 : int256 (evmShl 0x7e (evmAdd E1 TD1)) = 2 ^ 0x7e * int256 (evmAdd E1 TD1) :=
    shl126_transport (evmAdd_lt _ _) (le_of_lt (hadd1 ▸ hnum1)) hN1lt
  have hA2 : int256 (evmShl 0x7e (evmAdd E2 TD2)) = 2 ^ 0x7e * int256 (evmAdd E2 TD2) :=
    shl126_transport (evmAdd_lt _ _) (le_of_lt (hadd2 ▸ hnum2)) hN2lt
  have hA1pos : 0 < int256 (evmShl 0x7e (evmAdd E1 TD1)) := by
    rw [hA1]; exact Int.mul_pos (by positivity) (hadd1 ▸ hnum1)
  have hA2pos : 0 < int256 (evmShl 0x7e (evmAdd E2 TD2)) := by
    rw [hA2]; exact Int.mul_pos (by positivity) (hadd2 ▸ hnum2)
  -- both sdivs are floor divisions of nonnegative magnitudes
  rw [evmSdiv_pos_pos (evmShl_lt _ _) (evmSub_lt _ _) (le_of_lt hA1pos) hD1pos,
    evmSdiv_pos_pos (evmShl_lt _ _) (evmSub_lt _ _) (le_of_lt hA2pos) hD2pos]
  -- cross_to_div with the cross product A1·B2 ≤ A2·B1
  have hdd := cross_to_div (le_of_lt hA1pos) (le_of_lt hA2pos) hD1pos hD2pos (by
    rw [hA1, hA2, hsub1, hsub2, hadd1, hadd2]
    -- 2^126·(E1+TD1)·(E2−TD2) ≤ 2^126·(E2+TD2)·(E1−TD1) ⟺ tod1·ev2 ≤ tod2·ev1
    have hid1 := cross_identity (E1 : Int) (E2 : Int) (int256 TD1) (int256 TD2)
    nlinarith [hcross, hid1])
  exact_mod_cast hdd

end ExpYul
