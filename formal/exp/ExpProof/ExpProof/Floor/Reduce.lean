import ExpProof.Floor.Ln2Bound
import ExpProof.Floor.TBound
import ExpProof.Spec.RealExp

/-!
# The reduced-argument real identity (gap-1)

The runtime forms the reduced argument `t = tTree x` (Q128) and octave index `k = kTree x` so that
`exp(x/RAY) = 2^k · exp(rt)` with `rt = X/RAY − k·ln2` (`X = int256 x`). To fold the cert's
`exp(t/2¹²⁸)` bound onto the target, the reduced argument `rt` must coincide with `t/2¹²⁸` up to a
margin the runtime `MARGIN` absorbs:

```
|rt − t/2¹²⁸| < 2 / 2¹²⁸.
```

Decompose `rt − t/2¹²⁸ = P1 + P2 + P3`:

* `P1 = X·(1/RAY − K27/2²³⁵)` — the rational coefficient error over `|X| < 2⁹⁶`, below `2⁻¹³³`;
* `P2 = k·(LN2/2²³⁵ − ln2)` — the `ln2`-grid error (`0 ≤ ln2 − LN2/2²³⁵ < 2⁻²³⁵`, from `Ln2Bound`)
  over `|k| ≤ 63`, below `2⁻²²⁹`;
* `P3 = (K27·X − LN2·k)/2²³⁵ − t/2¹²⁸ ∈ [0, 1/2¹²⁸)` — the integer `t`-rounding sandwich.

The sum is below `2/2¹²⁸`.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Real

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The reduced argument `rt = X/RAY − k·ln2`. -/
def reducedArg (x : Nat) : Real :=
  (int256 x : Real) / (10 ^ 27 : Real) - (int256 (kTree x) : Real) * Real.log 2

/-- **Reduced-argument tight over bound (gap-1, one-sided).** On the meaningful region the integer
`t`-rounding residual `P3 ≥ 0` makes the over direction strictly tighter than the symmetric bound:
`t/2¹²⁸ − rt < 1/(32·2¹²⁸)` (the `ln2`-grid and rational errors alone, since `P3 ≥ 0` only helps).
This is the gap-1 contribution the joint never-over budget consumes. -/
theorem reducedArg_close_over {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (int256 (tTree x) : Real) / (2 ^ 128 : Real) - reducedArg x < 1 / (32 * (2 ^ 128 : Real)) := by
  obtain ⟨htlo, hthi⟩ := tTree_sandwich hx hC hC0
  obtain ⟨hklo, hkhi⟩ := kTree_bound hx hC hC0
  obtain ⟨hxlo, hxhi⟩ := region_x_bound hC hC0
  have hln2lo := ln2_lower
  have hln2hi := ln2_upper
  set t : Int := int256 (tTree x) with htdef
  set k : Int := int256 (kTree x) with hkdef
  set X : Int := int256 x with hXdef
  have hK : (0x279d346de4781f921dd7a89933d54d1f72928 : Int) = 55213970774324510299478046898216203619608872 := by norm_num
  have hL : (0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d : Int) =
      38271408169742254668347313025622401492114385419650052359639581444463709 := by norm_num
  rw [hK, hL] at htlo hthi
  -- ln2 bounds cleaned to decimal Real
  have hLN2decimal : ((LN2c : Nat) : Real) =
      38271408169742254668347313025622401492114385419650052359639581444463709 := by
    unfold LN2c; norm_num
  rw [hLN2decimal] at hln2lo hln2hi
  -- Real abbreviations
  set LR : Real := Real.log 2 with hLRdef
  set XR : Real := (X : Real) with hXRdef
  set kR : Real := (k : Real) with hkRdef
  set tR : Real := (t : Real) with htRdef
  -- numeric Real names
  set N235 : Real := (2 ^ 235 : Real) with hN235
  set N128 : Real := (2 ^ 128 : Real) with hN128
  set LN2R : Real := (38271408169742254668347313025622401492114385419650052359639581444463709 : Real) with hLN2R
  set K27R : Real := (55213970774324510299478046898216203619608872 : Real) with hK27R
  have hp235 : (0 : Real) < N235 := by rw [hN235]; positivity
  have hp128 : (0 : Real) < N128 := by rw [hN128]; positivity
  have hpRAY : (0 : Real) < (10 ^ 27 : Real) := by positivity
  -- 2^235 = 2^128 · 2^107
  have hsplit : N235 = N128 * 2 ^ 107 := by rw [hN235, hN128, ← pow_add]
  -- the three pieces
  set P1 : Real := XR * (1 / (10 ^ 27 : Real) - K27R / N235) with hP1def
  set P2 : Real := kR * (LN2R / N235 - LR) with hP2def
  set P3 : Real := (K27R * XR - LN2R * kR) / N235 - tR / N128 with hP3def
  -- identity: reducedArg x - t/2^128 = P1 + P2 + P3
  have hident : XR / (10 ^ 27 : Real) - kR * LR - tR / N128 = P1 + P2 + P3 := by
    rw [hP1def, hP2def, hP3def]; ring
  -- bound P1 : |P1| < 2^96·N/(2^235·10^27) where N = K27·10^27 − 2^235 = 222636907558699806209605632
  -- We bound P1 ∈ (−ε, ε) with ε = 2^96·N/(2^235·10^27) < 2⁻¹³².  Use explicit endpoints.
  have hXloR : -(79228162514264337593543950336 : Real) < XR := by
    have := (@Int.cast_lt Real _ _ _ _ _ _ _).mpr hxlo; rw [hXRdef]
    rw [show ((2:Int)^96 : Int) = 79228162514264337593543950336 from by norm_num] at this
    push_cast at this; linarith [this]
  have hXhiR : XR < (79228162514264337593543950336 : Real) := by
    have := (@Int.cast_lt Real _ _ _ _ _ _ _).mpr hxhi; rw [hXRdef]
    rw [show ((2:Int)^96 : Int) = 79228162514264337593543950336 from by norm_num] at this
    push_cast at this; linarith [this]
  -- coefficient: 1/10^27 − K27/2^235 < 0, magnitude m := (K27·10^27 − 2^235)/(2^235·10^27)
  have hcoeff_eq : (1 / (10 ^ 27 : Real) - K27R / N235) =
      -((K27R * (10 ^ 27 : Real) - N235) / (N235 * (10 ^ 27 : Real))) := by
    rw [hK27R, hN235]; field_simp; ring
  have hcoeff_num : K27R * (10 ^ 27 : Real) - N235 = 222636907558699806209605632 := by
    rw [hK27R, hN235]; norm_num
  -- |P1| < 2⁻¹³² (a generous bound):  |XR| < 2^96, |coeff| = m, and 2^96·m < 2⁻¹³².
  have hP1_abs : |P1| < 1 / (64 * N128) := by
    rw [hP1def, hcoeff_eq, hcoeff_num, abs_mul]
    have hden_pos : (0 : Real) < N235 * (10 ^ 27 : Real) := by positivity
    have hco_abs : |(-(222636907558699806209605632 / (N235 * (10 ^ 27 : Real))))| =
        222636907558699806209605632 / (N235 * (10 ^ 27 : Real)) := by
      rw [abs_neg, abs_of_pos (by positivity)]
    rw [hco_abs]
    have hX_abs : |XR| < 79228162514264337593543950336 := abs_lt.mpr ⟨hXloR, hXhiR⟩
    have hco_pos : (0:Real) < 222636907558699806209605632 / (N235 * (10 ^ 27 : Real)) := by positivity
    calc |XR| * (222636907558699806209605632 / (N235 * (10 ^ 27 : Real)))
        < 79228162514264337593543950336 * (222636907558699806209605632 / (N235 * (10 ^ 27 : Real))) :=
          (mul_lt_mul_right hco_pos).mpr hX_abs
      _ = 79228162514264337593543950336 * 222636907558699806209605632 /
            (N235 * (10 ^ 27 : Real)) := by rw [mul_div_assoc]
      _ < 1 / (64 * N128) := by
          rw [hN235, hN128, div_lt_div_iff₀ (by positivity) (by positivity)]; norm_num
  -- bound P2 : 0 ≤ LN2R/N235 − LR... actually ln2 ≥ LN2/2^235, so LN2R/N235 − LR ≤ 0, and ≥ −1/N235.
  have hP2_lo : LN2R / N235 - LR ≤ 0 := by linarith [hln2lo]
  have hP2_hi : -(1 / N235) ≤ LN2R / N235 - LR := by
    have : LR ≤ (LN2R + 1) / N235 := hln2hi
    rw [add_div] at this; linarith [this]
  -- |k| ≤ 63 ⇒ |P2| ≤ 63/N235 < 1/N128
  have hkloR : -(61 : Real) ≤ kR := by
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hklo; rw [hkRdef]; push_cast at this; linarith [this]
  have hkhiR : kR ≤ (63 : Real) := by
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hkhi; rw [hkRdef]; push_cast at this; linarith [this]
  have hP2_abs : |P2| < 1 / (64 * N128) := by
    rw [hP2def]
    have h1 : |kR| ≤ 63 := abs_le.mpr ⟨by linarith [hkloR], hkhiR⟩
    have h2 : |LN2R / N235 - LR| ≤ 1 / N235 := by
      rw [abs_le]
      refine ⟨by linarith [hP2_hi], ?_⟩
      have hpos : (0:Real) ≤ 1 / N235 := by positivity
      linarith [hP2_lo, hpos]
    have hbound : |kR * (LN2R / N235 - LR)| ≤ 63 * (1 / N235) := by
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    have hlt : 63 * (1 / N235) < 1 / (64 * N128) := by
      rw [hN235, hN128, mul_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]; norm_num
    linarith [hbound, hlt]
  -- bound P3 ∈ [0, 1/N128) from the integer sandwich
  have hP3int_lo : (0 : Int) ≤ 55213970774324510299478046898216203619608872 * X -
      38271408169742254668347313025622401492114385419650052359639581444463709 * k - 2 ^ 107 * t := by omega
  have hP3int_hi : 55213970774324510299478046898216203619608872 * X -
      38271408169742254668347313025622401492114385419650052359639581444463709 * k - 2 ^ 107 * t < 2 ^ 107 := by omega
  -- P3 = (A − 2^107·t)/N235, with the numerator (a Real cast of an Int) in [0, 2^107)
  have hnumR_lo : (0 : Real) ≤ K27R * XR - LN2R * kR - 2 ^ 107 * tR := by
    have h := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hP3int_lo
    rw [hK27R, hLN2R, hXRdef, hkRdef, htRdef]
    push_cast at h; linarith [h]
  have hnumR_hi : K27R * XR - LN2R * kR - 2 ^ 107 * tR < 2 ^ 107 := by
    have h := (@Int.cast_lt Real _ _ _ _ _ _ _).mpr hP3int_hi
    rw [hK27R, hLN2R, hXRdef, hkRdef, htRdef]
    push_cast at h; linarith [h]
  have hP3eq : P3 = (K27R * XR - LN2R * kR - 2 ^ 107 * tR) / N235 := by
    rw [hP3def, hsplit]; field_simp; ring
  have hP3_lo : 0 ≤ P3 := by rw [hP3eq]; exact div_nonneg hnumR_lo (le_of_lt hp235)
  have hP3_hi : P3 < 1 / N128 := by
    rw [hP3eq, hsplit, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hnumR_hi, hp128]
  -- assemble: tR/N128 − rt = −(P1+P2+P3) < 1/(32 N128), since P1+P2 > −1/(32 N128) and P3 ≥ 0
  have hP1 := abs_lt.mp hP1_abs
  have hP2 := abs_lt.mp hP2_abs
  clear_value N128 N235
  have he12 : (1 : Real) / (64 * N128) + 1 / (64 * N128) = 1 / (32 * N128) := by
    field_simp; ring
  have hredeq : reducedArg x = XR / (10 ^ 27 : Real) - kR * LR := rfl
  have hident' : (tR / N128 - reducedArg x) = -(P1 + P2 + P3) := by
    rw [hredeq]; linarith [hident]
  rw [hident']
  -- P1+P2 > −1/(32 N128); P3 ≥ 0
  have h12lo : -(1 / (32 * N128)) < P1 + P2 := by
    rw [show -(1 / (32 * N128)) = -(1 / (64 * N128)) + -(1 / (64 * N128)) from by rw [← he12]; ring]
    linarith [hP1.1, hP2.1]
  linarith [h12lo, hP3_lo]

/-- **Reduced-argument tight under bound (gap-1, one-sided).** The deficit direction: the integer
`t`-rounding residual `P3 ∈ [0, 1/2¹²⁸)` and the `ln2`-grid/rational errors `P1 + P2 < 1/(32·2¹²⁸)`
give `rt − t/2¹²⁸ < 33/(32·2¹²⁸)`. This is the gap-1 contribution the joint deficit budget
consumes (tighter than the symmetric `9/(8·2¹²⁸) = 36/(32·2¹²⁸)`). -/
theorem reducedArg_close_under {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    reducedArg x - (int256 (tTree x) : Real) / (2 ^ 128 : Real) < 33 / (32 * (2 ^ 128 : Real)) := by
  obtain ⟨htlo, hthi⟩ := tTree_sandwich hx hC hC0
  obtain ⟨hklo, hkhi⟩ := kTree_bound hx hC hC0
  obtain ⟨hxlo, hxhi⟩ := region_x_bound hC hC0
  have hln2lo := ln2_lower
  have hln2hi := ln2_upper
  set t : Int := int256 (tTree x) with htdef
  set k : Int := int256 (kTree x) with hkdef
  set X : Int := int256 x with hXdef
  have hK : (0x279d346de4781f921dd7a89933d54d1f72928 : Int) = 55213970774324510299478046898216203619608872 := by norm_num
  have hL : (0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d : Int) =
      38271408169742254668347313025622401492114385419650052359639581444463709 := by norm_num
  rw [hK, hL] at htlo hthi
  have hLN2decimal : ((LN2c : Nat) : Real) =
      38271408169742254668347313025622401492114385419650052359639581444463709 := by
    unfold LN2c; norm_num
  rw [hLN2decimal] at hln2lo hln2hi
  set LR : Real := Real.log 2 with hLRdef
  set XR : Real := (X : Real) with hXRdef
  set kR : Real := (k : Real) with hkRdef
  set tR : Real := (t : Real) with htRdef
  set N235 : Real := (2 ^ 235 : Real) with hN235
  set N128 : Real := (2 ^ 128 : Real) with hN128
  set LN2R : Real := (38271408169742254668347313025622401492114385419650052359639581444463709 : Real) with hLN2R
  set K27R : Real := (55213970774324510299478046898216203619608872 : Real) with hK27R
  have hp235 : (0 : Real) < N235 := by rw [hN235]; positivity
  have hp128 : (0 : Real) < N128 := by rw [hN128]; positivity
  have hpRAY : (0 : Real) < (10 ^ 27 : Real) := by positivity
  have hsplit : N235 = N128 * 2 ^ 107 := by rw [hN235, hN128, ← pow_add]
  set P1 : Real := XR * (1 / (10 ^ 27 : Real) - K27R / N235) with hP1def
  set P2 : Real := kR * (LN2R / N235 - LR) with hP2def
  set P3 : Real := (K27R * XR - LN2R * kR) / N235 - tR / N128 with hP3def
  have hident : XR / (10 ^ 27 : Real) - kR * LR - tR / N128 = P1 + P2 + P3 := by
    rw [hP1def, hP2def, hP3def]; ring
  have hXloR : -(79228162514264337593543950336 : Real) < XR := by
    have := (@Int.cast_lt Real _ _ _ _ _ _ _).mpr hxlo; rw [hXRdef]
    rw [show ((2:Int)^96 : Int) = 79228162514264337593543950336 from by norm_num] at this
    push_cast at this; linarith [this]
  have hXhiR : XR < (79228162514264337593543950336 : Real) := by
    have := (@Int.cast_lt Real _ _ _ _ _ _ _).mpr hxhi; rw [hXRdef]
    rw [show ((2:Int)^96 : Int) = 79228162514264337593543950336 from by norm_num] at this
    push_cast at this; linarith [this]
  have hcoeff_eq : (1 / (10 ^ 27 : Real) - K27R / N235) =
      -((K27R * (10 ^ 27 : Real) - N235) / (N235 * (10 ^ 27 : Real))) := by
    rw [hK27R, hN235]; field_simp; ring
  have hcoeff_num : K27R * (10 ^ 27 : Real) - N235 = 222636907558699806209605632 := by
    rw [hK27R, hN235]; norm_num
  have hP1_abs : |P1| < 1 / (64 * N128) := by
    rw [hP1def, hcoeff_eq, hcoeff_num, abs_mul]
    have hden_pos : (0 : Real) < N235 * (10 ^ 27 : Real) := by positivity
    have hco_abs : |(-(222636907558699806209605632 / (N235 * (10 ^ 27 : Real))))| =
        222636907558699806209605632 / (N235 * (10 ^ 27 : Real)) := by
      rw [abs_neg, abs_of_pos (by positivity)]
    rw [hco_abs]
    have hX_abs : |XR| < 79228162514264337593543950336 := abs_lt.mpr ⟨hXloR, hXhiR⟩
    have hco_pos : (0:Real) < 222636907558699806209605632 / (N235 * (10 ^ 27 : Real)) := by positivity
    calc |XR| * (222636907558699806209605632 / (N235 * (10 ^ 27 : Real)))
        < 79228162514264337593543950336 * (222636907558699806209605632 / (N235 * (10 ^ 27 : Real))) :=
          (mul_lt_mul_right hco_pos).mpr hX_abs
      _ = 79228162514264337593543950336 * 222636907558699806209605632 /
            (N235 * (10 ^ 27 : Real)) := by rw [mul_div_assoc]
      _ < 1 / (64 * N128) := by
          rw [hN235, hN128, div_lt_div_iff₀ (by positivity) (by positivity)]; norm_num
  have hP2_lo : LN2R / N235 - LR ≤ 0 := by linarith [hln2lo]
  have hP2_hi : -(1 / N235) ≤ LN2R / N235 - LR := by
    have : LR ≤ (LN2R + 1) / N235 := hln2hi
    rw [add_div] at this; linarith [this]
  have hkloR : -(61 : Real) ≤ kR := by
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hklo; rw [hkRdef]; push_cast at this; linarith [this]
  have hkhiR : kR ≤ (63 : Real) := by
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hkhi; rw [hkRdef]; push_cast at this; linarith [this]
  have hP2_abs : |P2| < 1 / (64 * N128) := by
    rw [hP2def]
    have h1 : |kR| ≤ 63 := abs_le.mpr ⟨by linarith [hkloR], hkhiR⟩
    have h2 : |LN2R / N235 - LR| ≤ 1 / N235 := by
      rw [abs_le]
      refine ⟨by linarith [hP2_hi], ?_⟩
      have hpos : (0:Real) ≤ 1 / N235 := by positivity
      linarith [hP2_lo, hpos]
    have hbound : |kR * (LN2R / N235 - LR)| ≤ 63 * (1 / N235) := by
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    have hlt : 63 * (1 / N235) < 1 / (64 * N128) := by
      rw [hN235, hN128, mul_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]; norm_num
    linarith [hbound, hlt]
  have hP3int_hi : 55213970774324510299478046898216203619608872 * X -
      38271408169742254668347313025622401492114385419650052359639581444463709 * k - 2 ^ 107 * t < 2 ^ 107 := by omega
  have hnumR_hi : K27R * XR - LN2R * kR - 2 ^ 107 * tR < 2 ^ 107 := by
    have h := (@Int.cast_lt Real _ _ _ _ _ _ _).mpr hP3int_hi
    rw [hK27R, hLN2R, hXRdef, hkRdef, htRdef]
    push_cast at h; linarith [h]
  have hP3eq : P3 = (K27R * XR - LN2R * kR - 2 ^ 107 * tR) / N235 := by
    rw [hP3def, hsplit]; field_simp; ring
  have hP3_hi : P3 < 1 / N128 := by
    rw [hP3eq, hsplit, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hnumR_hi, hp128]
  -- assemble: rt − t/2^128 = P1+P2+P3 < 1/(32 N128) + 1/N128 = 33/(32 N128)
  have hP1 := abs_lt.mp hP1_abs
  have hP2 := abs_lt.mp hP2_abs
  clear_value N128 N235
  have he12 : (1 : Real) / (64 * N128) + 1 / (64 * N128) = 1 / (32 * N128) := by
    field_simp; ring
  have h1_32N : (1 : Real) / (32 * N128) + 1 / N128 = 33 / (32 * N128) := by
    field_simp; ring
  have hredeq : reducedArg x = XR / (10 ^ 27 : Real) - kR * LR := rfl
  have hident' : (reducedArg x - tR / N128) = P1 + P2 + P3 := by
    rw [hredeq]; linarith [hident]
  rw [hident']
  have h12 : P1 + P2 < 1 / (32 * N128) := by rw [← he12]; linarith [hP1.2, hP2.2]
  rw [← h1_32N]; linarith [h12, hP3_hi]

/-- info: 'ExpYul.reducedArg_close_under' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reducedArg_close_under

/-- **Reduced-argument real bound (gap-1).** On the meaningful region the reduced argument `rt`
agrees with `t/2¹²⁸` to within `9/(8·2¹²⁸)` (the integer `t`-rounding sandwich `[0, 1/2¹²⁸)`
dominates; the rational and `ln2`-grid errors are below `2⁻¹³²`). -/
theorem reducedArg_close {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    |reducedArg x - (int256 (tTree x) : Real) / (2 ^ 128 : Real)| < 9 / (8 * (2 ^ 128 : Real)) := by
  obtain ⟨htlo, hthi⟩ := tTree_sandwich hx hC hC0
  obtain ⟨hklo, hkhi⟩ := kTree_bound hx hC hC0
  obtain ⟨hxlo, hxhi⟩ := region_x_bound hC hC0
  have hln2lo := ln2_lower
  have hln2hi := ln2_upper
  set t : Int := int256 (tTree x) with htdef
  set k : Int := int256 (kTree x) with hkdef
  set X : Int := int256 x with hXdef
  have hK : (0x279d346de4781f921dd7a89933d54d1f72928 : Int) = 55213970774324510299478046898216203619608872 := by norm_num
  have hL : (0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d : Int) =
      38271408169742254668347313025622401492114385419650052359639581444463709 := by norm_num
  rw [hK, hL] at htlo hthi
  -- ln2 bounds cleaned to decimal Real
  have hLN2decimal : ((LN2c : Nat) : Real) =
      38271408169742254668347313025622401492114385419650052359639581444463709 := by
    unfold LN2c; norm_num
  rw [hLN2decimal] at hln2lo hln2hi
  -- Real abbreviations
  set LR : Real := Real.log 2 with hLRdef
  set XR : Real := (X : Real) with hXRdef
  set kR : Real := (k : Real) with hkRdef
  set tR : Real := (t : Real) with htRdef
  -- numeric Real names
  set N235 : Real := (2 ^ 235 : Real) with hN235
  set N128 : Real := (2 ^ 128 : Real) with hN128
  set LN2R : Real := (38271408169742254668347313025622401492114385419650052359639581444463709 : Real) with hLN2R
  set K27R : Real := (55213970774324510299478046898216203619608872 : Real) with hK27R
  have hp235 : (0 : Real) < N235 := by rw [hN235]; positivity
  have hp128 : (0 : Real) < N128 := by rw [hN128]; positivity
  have hpRAY : (0 : Real) < (10 ^ 27 : Real) := by positivity
  -- 2^235 = 2^128 · 2^107
  have hsplit : N235 = N128 * 2 ^ 107 := by rw [hN235, hN128, ← pow_add]
  -- the three pieces
  set P1 : Real := XR * (1 / (10 ^ 27 : Real) - K27R / N235) with hP1def
  set P2 : Real := kR * (LN2R / N235 - LR) with hP2def
  set P3 : Real := (K27R * XR - LN2R * kR) / N235 - tR / N128 with hP3def
  -- identity: reducedArg x - t/2^128 = P1 + P2 + P3
  have hident : XR / (10 ^ 27 : Real) - kR * LR - tR / N128 = P1 + P2 + P3 := by
    rw [hP1def, hP2def, hP3def]; ring
  -- bound P1 : |P1| < 2^96·N/(2^235·10^27) where N = K27·10^27 − 2^235 = 222636907558699806209605632
  -- We bound P1 ∈ (−ε, ε) with ε = 2^96·N/(2^235·10^27) < 2⁻¹³².  Use explicit endpoints.
  have hXloR : -(79228162514264337593543950336 : Real) < XR := by
    have := (@Int.cast_lt Real _ _ _ _ _ _ _).mpr hxlo; rw [hXRdef]
    rw [show ((2:Int)^96 : Int) = 79228162514264337593543950336 from by norm_num] at this
    push_cast at this; linarith [this]
  have hXhiR : XR < (79228162514264337593543950336 : Real) := by
    have := (@Int.cast_lt Real _ _ _ _ _ _ _).mpr hxhi; rw [hXRdef]
    rw [show ((2:Int)^96 : Int) = 79228162514264337593543950336 from by norm_num] at this
    push_cast at this; linarith [this]
  -- coefficient: 1/10^27 − K27/2^235 < 0, magnitude m := (K27·10^27 − 2^235)/(2^235·10^27)
  have hcoeff_eq : (1 / (10 ^ 27 : Real) - K27R / N235) =
      -((K27R * (10 ^ 27 : Real) - N235) / (N235 * (10 ^ 27 : Real))) := by
    rw [hK27R, hN235]; field_simp; ring
  have hcoeff_num : K27R * (10 ^ 27 : Real) - N235 = 222636907558699806209605632 := by
    rw [hK27R, hN235]; norm_num
  -- |P1| < 2⁻¹³² (a generous bound):  |XR| < 2^96, |coeff| = m, and 2^96·m < 2⁻¹³².
  have hP1_abs : |P1| < 1 / (64 * N128) := by
    rw [hP1def, hcoeff_eq, hcoeff_num, abs_mul]
    have hden_pos : (0 : Real) < N235 * (10 ^ 27 : Real) := by positivity
    have hco_abs : |(-(222636907558699806209605632 / (N235 * (10 ^ 27 : Real))))| =
        222636907558699806209605632 / (N235 * (10 ^ 27 : Real)) := by
      rw [abs_neg, abs_of_pos (by positivity)]
    rw [hco_abs]
    have hX_abs : |XR| < 79228162514264337593543950336 := abs_lt.mpr ⟨hXloR, hXhiR⟩
    have hco_pos : (0:Real) < 222636907558699806209605632 / (N235 * (10 ^ 27 : Real)) := by positivity
    calc |XR| * (222636907558699806209605632 / (N235 * (10 ^ 27 : Real)))
        < 79228162514264337593543950336 * (222636907558699806209605632 / (N235 * (10 ^ 27 : Real))) :=
          (mul_lt_mul_right hco_pos).mpr hX_abs
      _ = 79228162514264337593543950336 * 222636907558699806209605632 /
            (N235 * (10 ^ 27 : Real)) := by rw [mul_div_assoc]
      _ < 1 / (64 * N128) := by
          rw [hN235, hN128, div_lt_div_iff₀ (by positivity) (by positivity)]; norm_num
  -- bound P2 : 0 ≤ LN2R/N235 − LR... actually ln2 ≥ LN2/2^235, so LN2R/N235 − LR ≤ 0, and ≥ −1/N235.
  have hP2_lo : LN2R / N235 - LR ≤ 0 := by linarith [hln2lo]
  have hP2_hi : -(1 / N235) ≤ LN2R / N235 - LR := by
    have : LR ≤ (LN2R + 1) / N235 := hln2hi
    rw [add_div] at this; linarith [this]
  -- |k| ≤ 63 ⇒ |P2| ≤ 63/N235 < 1/N128
  have hkloR : -(61 : Real) ≤ kR := by
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hklo; rw [hkRdef]; push_cast at this; linarith [this]
  have hkhiR : kR ≤ (63 : Real) := by
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hkhi; rw [hkRdef]; push_cast at this; linarith [this]
  have hP2_abs : |P2| < 1 / (64 * N128) := by
    rw [hP2def]
    have h1 : |kR| ≤ 63 := abs_le.mpr ⟨by linarith [hkloR], hkhiR⟩
    have h2 : |LN2R / N235 - LR| ≤ 1 / N235 := by
      rw [abs_le]
      refine ⟨by linarith [hP2_hi], ?_⟩
      have hpos : (0:Real) ≤ 1 / N235 := by positivity
      linarith [hP2_lo, hpos]
    have hbound : |kR * (LN2R / N235 - LR)| ≤ 63 * (1 / N235) := by
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    have hlt : 63 * (1 / N235) < 1 / (64 * N128) := by
      rw [hN235, hN128, mul_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]; norm_num
    linarith [hbound, hlt]
  -- bound P3 ∈ [0, 1/N128) from the integer sandwich
  have hP3int_lo : (0 : Int) ≤ 55213970774324510299478046898216203619608872 * X -
      38271408169742254668347313025622401492114385419650052359639581444463709 * k - 2 ^ 107 * t := by omega
  have hP3int_hi : 55213970774324510299478046898216203619608872 * X -
      38271408169742254668347313025622401492114385419650052359639581444463709 * k - 2 ^ 107 * t < 2 ^ 107 := by omega
  -- P3 = (A − 2^107·t)/N235, with the numerator (a Real cast of an Int) in [0, 2^107)
  have hnumR_lo : (0 : Real) ≤ K27R * XR - LN2R * kR - 2 ^ 107 * tR := by
    have h := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hP3int_lo
    rw [hK27R, hLN2R, hXRdef, hkRdef, htRdef]
    push_cast at h; linarith [h]
  have hnumR_hi : K27R * XR - LN2R * kR - 2 ^ 107 * tR < 2 ^ 107 := by
    have h := (@Int.cast_lt Real _ _ _ _ _ _ _).mpr hP3int_hi
    rw [hK27R, hLN2R, hXRdef, hkRdef, htRdef]
    push_cast at h; linarith [h]
  have hP3eq : P3 = (K27R * XR - LN2R * kR - 2 ^ 107 * tR) / N235 := by
    rw [hP3def, hsplit]; field_simp; ring
  have hP3_lo : 0 ≤ P3 := by rw [hP3eq]; exact div_nonneg hnumR_lo (le_of_lt hp235)
  have hP3_hi : P3 < 1 / N128 := by
    rw [hP3eq, hsplit, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hnumR_hi, hp128]
  -- assemble
  show |reducedArg x - tR / N128| < 9 / (8 * N128)
  rw [show reducedArg x = XR / (10 ^ 27 : Real) - kR * LR from rfl]
  rw [hident, abs_lt]
  have hP1 := abs_lt.mp hP1_abs
  have hP2 := abs_lt.mp hP2_abs
  clear_value N128 N235
  -- P1+P2 < 2/(64N) = 1/(32N); P3 ∈ [0, 1/N).  9/(8N) = 36/(32N) covers 33/(32N).
  have hp128' : (0 : Real) < 1 / N128 := by positivity
  -- 1/(64N)+1/(64N) ≤ 1/(32N) ≤ 1/(8N)
  have he12 : (1 : Real) / (64 * N128) + 1 / (64 * N128) = 1 / (32 * N128) := by
    field_simp; ring
  have h32_8 : (1 : Real) / (32 * N128) ≤ 1 / (8 * N128) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith [hp128]
  have h1_8N : (1 : Real) / N128 + 1 / (8 * N128) = 9 / (8 * N128) := by
    field_simp; ring
  have hsum_hi : P1 + P2 + P3 < 9 / (8 * N128) := by
    have h12 : P1 + P2 < 1 / (8 * N128) := by
      have : P1 + P2 < 1 / (32 * N128) := by rw [← he12]; linarith [hP1.2, hP2.2]
      linarith [this, h32_8]
    rw [← h1_8N]; linarith [h12, hP3_hi]
  have hsum_lo : -(9 / (8 * N128)) < P1 + P2 + P3 := by
    have h12 : -(1 / (8 * N128)) < P1 + P2 := by
      have hlo : -(1 / (32 * N128)) < P1 + P2 := by
        rw [show -(1 / (32 * N128)) = -(1 / (64 * N128)) + -(1 / (64 * N128)) from by rw [← he12]; ring]
        linarith [hP1.1, hP2.1]
      linarith [hlo, h32_8]
    have hneg : -(9 / (8 * N128)) < -(1 / (8 * N128)) + 0 := by
      rw [← h1_8N]; linarith [hp128']
    linarith [h12, hP3_lo, hneg]
  exact ⟨hsum_lo, hsum_hi⟩

/-- info: 'ExpYul.reducedArg_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reducedArg_close

end

end ExpYul
