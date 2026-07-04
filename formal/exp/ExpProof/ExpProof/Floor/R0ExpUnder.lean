import ExpProof.Floor.R0Exp

/-!
# The deficit (under) side of the per-point `r0`-vs-`exp` bridge, and the seam bound

This module contains the counterpart to the never-over `r0_real_over_within`: the per-point deficit
`scaleQ68·exp(rt) ≤ r0 + 33/4` (`r0_real_under_within`), both signs, with the same four-link chain:

1. link-1 deficit against the grid rational including the `div` floor, `≤ 6210/1000`;
2. the argument granularity (`Floor.GranV`) — free on the `t ≥ 0` half, `≤ (5¹⁸/2⁴⁰)·1644901622230542074/10¹⁹`
   (`Mp`-folded) on the `t ≤ 0` half;
3. the `Mp` factor, `≤ 2/25` (via `r0 ≤ 1.45·scaleQ68`);
4. the under-direction reduced-argument gap, `≤ 1267/1000` (via `exp(rt) ≤ √2·(1+ε)`).

The sum `6210/1000 + 2/25 + (5¹⁸/2⁴⁰)·1644901622230542074/10¹⁹ + 1267/1000 ≤ 33/4` feeds the `k = 64` deficit
envelope `(33/4 + MARGIN)/2⁴ < 1`. The module closes with the octave-seam `r0`-doubling
bound `r0₁ + 3 ≤ 2·r0₂` (`SeamR0Bound`), where the `1 − exp(−1/RAY)` seam slack (≈ `8.5·10¹⁰` grid
units against `r0₂ > 2¹²⁶`) dwarfs both per-point budgets and the three integer units.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Poly

set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 2000

noncomputable section

/-- `exp(reducedArg) ≤ 14143/10000` (both signs). The reduced argument is within a half-octave,
`reducedArg ≤ log2/2 + 33/(32·2¹²⁸)`, so `exp` is at most `√2·(1+ε)`, which the `14143/10000`
ceiling covers with room. Drives the under gap-1. -/
theorem exp_reducedArg_le_sqrt2bound {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    Real.exp (reducedArg x) ≤ 14143 / 10000 := by
  have hclose := abs_lt.mp (reducedArg_close hx hC hC0)
  have hthalf : (int256 (tTree x) : Real) / (2 ^ 128 : Real) ≤ Real.log 2 / 2 := by
    rcases le_or_gt 0 (int256 (tTree x)) with htnn | htneg
    · exact t_over_2128_le_half_log2 hx hC hC0
    · have htle : (int256 (tTree x) : Real) ≤ 0 := by exact_mod_cast le_of_lt htneg
      have hlog2 : (0:Real) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have : (int256 (tTree x) : Real) / (2 ^ 128 : Real) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg htle (by positivity)
      linarith [this, hlog2]
  set u : Real := 9 / (8 * (2 ^ 128 : Real)) with hu
  have hupos : (0:Real) < u := by rw [hu]; positivity
  have husmall : u ≤ 1 / 100000 := by rw [hu, div_le_div_iff₀ (by positivity) (by norm_num)]; norm_num
  clear_value u
  have hrt : reducedArg x ≤ Real.log 2 / 2 + u := by linarith [hclose.2, hthalf]
  have hmono : Real.exp (reducedArg x) ≤ Real.exp (Real.log 2 / 2 + u) := Real.exp_le_exp.mpr hrt
  have hsplit : Real.exp (Real.log 2 / 2 + u) = Real.sqrt 2 * Real.exp u := by
    rw [Real.exp_add]; congr 1
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0:Real) < 2)]; ring_nf
  have hep : (0:Real) < Real.exp u := Real.exp_pos u
  have h1u : (0:Real) < 1 - u := by
    have : (1:Real) / 100000 < 1 := by norm_num
    linarith [husmall, this]
  have hexpu : Real.exp u ≤ 1 / (1 - u) := by
    have h1 : (1 : Real) - u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
    rw [Real.exp_neg] at h1
    have h2 : (1 - u) * Real.exp u ≤ 1 := by
      have := mul_le_mul_of_nonneg_right h1 (le_of_lt hep)
      rwa [inv_mul_cancel₀ (ne_of_gt hep)] at this
    rw [le_div_iff₀ h1u]; linarith [h2]
  have hsqrt2 : Real.sqrt 2 ≤ 141422 / 100000 := by rw [Real.sqrt_le_iff]; constructor <;> norm_num
  calc Real.exp (reducedArg x) ≤ Real.sqrt 2 * Real.exp u := by rw [← hsplit]; exact hmono
    _ ≤ (141422 / 100000) * (1 / (1 - u)) :=
        mul_le_mul hsqrt2 hexpu (le_of_lt hep) (by norm_num)
    _ ≤ 14143 / 10000 := by
        rw [mul_one_div, div_le_div_iff₀ h1u (by norm_num)]; nlinarith [husmall]

/-! ## The `r0` bracket on the nonneg half -/

/-- `r0` is bracketed on the nonneg half: `scaleQ68 ≤ r0` and `100·r0 ≤ 145·scaleQ68`. -/
theorem r0_bracket_nonneg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    (0xde0b6b3a764000000000000000000000 : Int) ≤ int256 (r0Tree x) ∧
      100 * (int256 (r0Tree x)) ≤ 145 * (0xde0b6b3a764000000000000000000000 : Int) := by
  obtain ⟨hfloor_lo, hfloor_hi⟩ := r0_floor_sandwich hx hC hC0
  have h145 := num_le_145_den hx hC hC0 htnn
  set r0 := int256 (r0Tree x) with hr0def
  set ev := (evTree x : Int) with hevdef
  set tod := int256 (todTree x) with htoddef
  have hden072 : (165038630930342071346895739193146786696 : Int) ≤ ev - tod := by
    have := den_ge_194 hx hC hC0; rw [← hevdef, ← htoddef] at this; exact this
  have hdenpos : (0:Int) < ev - tod := lt_of_lt_of_le (by norm_num) hden072
  -- tod ≥ 0 on nonneg half
  have htodnn : (0:Int) ≤ tod := by
    obtain ⟨_, _, htodlo, _⟩ := todTree_bound hx hC hC0
    have hodnn : (0:Int) ≤ (odTree x : Int) := Int.natCast_nonneg _
    have htod : (2 ^ 129 : Int) * tod ≤ int256 (tTree x) * (odTree x : Int) := htodlo
    have hpos : (0:Int) ≤ int256 (tTree x) * (odTree x : Int) := mul_nonneg htnn hodnn
    nlinarith [htod, hpos]
  refine ⟨?_, ?_⟩
  · -- 2^126 ≤ r0:  2^126·num < (r0+1)·den, num ≥ den ⟹ 2^126·den < (r0+1)·den ⟹ 2^126 < r0+1
    have hnumden : (0xde0b6b3a764000000000000000000000 : Int) * (ev - tod) ≤ (0xde0b6b3a764000000000000000000000 : Int) * (ev + tod) := by nlinarith [htodnn]
    have h : (0xde0b6b3a764000000000000000000000 : Int) * (ev - tod) < (r0 + 1) * (ev - tod) := lt_of_le_of_lt hnumden hfloor_hi
    have := lt_of_mul_lt_mul_right h (le_of_lt hdenpos)
    omega
  · -- 100·r0 ≤ 145·2^126:  100·r0·den ≤ 100·2^126·num ≤ 2^126·145·den
    have h1 : 100 * (r0 * (ev - tod)) ≤ 100 * ((0xde0b6b3a764000000000000000000000 : Int) * (ev + tod)) :=
      mul_le_mul_of_nonneg_left hfloor_lo (by norm_num)
    have h2 : (0xde0b6b3a764000000000000000000000 : Int) * (100 * (ev + tod)) ≤ (0xde0b6b3a764000000000000000000000 : Int) * (145 * (ev - tod)) :=
      mul_le_mul_of_nonneg_left h145 (by positivity)
    have hchain : 100 * r0 * (ev - tod) ≤ 145 * (0xde0b6b3a764000000000000000000000 : Int) * (ev - tod) := by nlinarith [h1, h2]
    exact le_of_mul_le_mul_right hchain hdenpos

/-! ## Link 1 (under side): the grid rational vs `r0` -/

/-- **Link-1 under (nonneg half)**: `1000·(scaleQ68·NUMv − r0·DENv) ≤ 6210·DENv`. The floor residual
costs one denominator; the odd-truncation carry `(2⁶³⁷ + Wod·2⁴⁸⁰·t)·(scaleQ68 + r0)` fits in `1.49`
denominators (`t ≤ H128`, `r0 ≤ 1.45·scaleQ68`, `den ≥ 1.94·scaleQ68`). -/
theorem link1_under_int {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    1000 * ((0xde0b6b3a764000000000000000000000 : Int) * NUMv (vTree x) (int256 (tTree x)) -
        int256 (r0Tree x) * DENv (vTree x) (int256 (tTree x))) ≤
      6210 * DENv (vTree x) (int256 (tTree x)) := by
  obtain ⟨_, hfloor_hi⟩ := r0_floor_sandwich hx hC hC0
  obtain ⟨hEp_lo, _, _, _⟩ := bridge_facts hx hC hC0
  obtain ⟨_, htOp_hi⟩ := tOd_bracket_nonneg hx hC hC0 htnn
  obtain ⟨hr0lo, hr0hi145⟩ := r0_bracket_nonneg hx hC hC0 htnn
  obtain ⟨hDEN_ge, _⟩ := DENv_runtime_bracket hx hC hC0 htnn
  obtain ⟨_, hthi⟩ := tTree_in_cert_domain hx hC hC0
  have hden := den_ge_194 hx hC hC0
  have hLHS : (0xde0b6b3a764000000000000000000000 : Int) * NUMv (vTree x) (int256 (tTree x)) -
      int256 (r0Tree x) * DENv (vTree x) (int256 (tTree x)) ≤
      2 ^ 637 * ((evTree x : Int) - int256 (todTree x)) +
        (2 ^ 637 + 269746241 * 2 ^ 480 * int256 (tTree x)) * ((0xde0b6b3a764000000000000000000000 : Int) + int256 (r0Tree x)) := by
    unfold NUMv DENv
    set r0 := int256 (r0Tree x) with hr0def
    set ev := (evTree x : Int) with hevdef
    set tod := int256 (todTree x) with htoddef
    set t := int256 (tTree x) with htdef
    set Ep := (evNumV (vTree x) : Int) with hEpdef
    set Op := (odNumV (vTree x) : Int) with hOpdef
    have h2126r0_np : (0xde0b6b3a764000000000000000000000 : Int) - r0 ≤ 0 := by linarith [hr0lo]
    have hr0p_nn : (0:Int) ≤ (0xde0b6b3a764000000000000000000000 : Int) + r0 := by linarith [hr0lo]
    -- Ep·2^110·(2^126−r0) ≤ 2^637·ev·(2^126−r0)
    have hterm1 : Ep * 2 ^ 110 * ((0xde0b6b3a764000000000000000000000 : Int) - r0) ≤ 2 ^ 637 * ev * ((0xde0b6b3a764000000000000000000000 : Int) - r0) := by
      apply mul_le_mul_of_nonpos_right _ h2126r0_np
      nlinarith [hEp_lo]
    -- t·Op·(2^126+r0) ≤ (2^637·tod + 2^637 + Wod·2^480·t)·(2^126+r0)
    have hterm2 : t * Op * ((0xde0b6b3a764000000000000000000000 : Int) + r0) ≤
        (2 ^ 637 * tod + 2 ^ 637 + 269746241 * 2 ^ 480 * t) * ((0xde0b6b3a764000000000000000000000 : Int) + r0) :=
      mul_le_mul_of_nonneg_right htOp_hi hr0p_nn
    -- floor: 2^126·num − r0·den < den, scaled by 2^637
    have hfloor : (0xde0b6b3a764000000000000000000000 : Int) * (ev + tod) - r0 * (ev - tod) ≤ (ev - tod) := by
      linarith [hfloor_hi]
    have hfloor638 : (2:Int) ^ 637 * ((0xde0b6b3a764000000000000000000000 : Int) * (ev + tod) - r0 * (ev - tod)) ≤
        2 ^ 637 * (ev - tod) := mul_le_mul_of_nonneg_left hfloor (by positivity)
    nlinarith [hterm1, hterm2, hfloor638]
  -- budget the two additive pieces against DENv
  set r0 := int256 (r0Tree x) with hr0def
  set t := int256 (tTree x) with htdef
  set den := (evTree x : Int) - int256 (todTree x) with hdendef
  set D := DENv (vTree x) t with hDdef
  have hA : 2 ^ 637 * den ≤ D + 2 * 2 ^ 637 := by rw [hDdef]; linarith [hDEN_ge]
  have hDlow : (2:Int) ^ 637 * (165038630930342071346895739193146786696 - 2) ≤ D := by
    have h1 : (2:Int) ^ 637 * (165038630930342071346895739193146786696 - 2) ≤
        2 ^ 637 * den - 2 * 2 ^ 637 := by nlinarith [hden]
    rw [hDdef]; linarith [h1, hDEN_ge]
  have hB : 100 * ((2 ^ 637 + 269746241 * 2 ^ 480 * t) * ((0xde0b6b3a764000000000000000000000 : Int) + r0)) ≤ 520 * D := by
    have hcoef : 2 ^ 637 + 269746241 * 2 ^ 480 * t ≤
        2 ^ 637 + 269746241 * 2 ^ 480 * 117932881612756647068972071382077242199 := by
      have := mul_le_mul_of_nonneg_left hthi (by positivity : (0:Int) ≤ 269746241 * 2 ^ 480)
      linarith [this]
    have hr0p_nn : (0:Int) ≤ (0xde0b6b3a764000000000000000000000 : Int) + r0 := by linarith [(r0_bracket_nonneg hx hC hC0 htnn).1]
    have h1 : (2 ^ 637 + 269746241 * 2 ^ 480 * t) * ((0xde0b6b3a764000000000000000000000 : Int) + r0) ≤
        (2 ^ 637 + 269746241 * 2 ^ 480 * 117932881612756647068972071382077242199) *
          ((0xde0b6b3a764000000000000000000000 : Int) + r0) := mul_le_mul_of_nonneg_right hcoef hr0p_nn
    have h2 : 100 * ((2 ^ 637 + 269746241 * 2 ^ 480 * 117932881612756647068972071382077242199) *
        ((0xde0b6b3a764000000000000000000000 : Int) + r0)) ≤
        (2 ^ 637 + 269746241 * 2 ^ 480 * 117932881612756647068972071382077242199) *
          (245 * (0xde0b6b3a764000000000000000000000 : Int)) := by
      have hr0cap : 100 * ((0xde0b6b3a764000000000000000000000 : Int) + r0) ≤ 245 * (0xde0b6b3a764000000000000000000000 : Int) := by linarith [hr0hi145]
      nlinarith [hr0cap]
    have h3 : (2 ^ 637 + 269746241 * 2 ^ 480 * 117932881612756647068972071382077242199) *
        (245 * (0xde0b6b3a764000000000000000000000 : Int)) ≤ 520 * (2 ^ 637 * (165038630930342071346895739193146786696 - 2)) := by
      norm_num
    have h4 : (520 : Int) * (2 ^ 637 * (165038630930342071346895739193146786696 - 2)) ≤ 520 * D :=
      mul_le_mul_of_nonneg_left hDlow (by norm_num)
    linarith [h1, h2, h3, h4]
  have hC2000 : (2000 : Int) * 2 ^ 637 ≤ D := by
    have : (2000 : Int) * 2 ^ 637 ≤ 2 ^ 637 * (165038630930342071346895739193146786696 - 2) := by
      norm_num
    linarith [this, hDlow]
  linarith [hLHS, hA, hB, hC2000]

/-- **Link-1 under (nonpositive half)**: the same `6210/1000` budget; the even-truncation width and
the `tod`-floor unit are absorbed by `DENv ≥ 2⁶³⁷·ev ≥ 2⁶³⁷·A0`. -/
theorem link1_under_int_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) :
    1000 * ((0xde0b6b3a764000000000000000000000 : Int) * NUMv (vTree x) (int256 (tTree x)) -
        int256 (r0Tree x) * DENv (vTree x) (int256 (tTree x))) ≤
      6210 * DENv (vTree x) (int256 (tTree x)) := by
  obtain ⟨_, hfloor_hi⟩ := r0_floor_sandwich hx hC hC0
  obtain ⟨hEp_lo, hEp_hi, _, _⟩ := bridge_facts hx hC hC0
  obtain ⟨htOp_hi, _⟩ := tOd_bracket_neg hx hC hC0 htneg
  have hr0le := r0_le_scale_neg hx hC hC0 htneg
  obtain ⟨hr0lo, _⟩ := r0Tree_bounds hx hC hC0
  have hDEN_ge := DENv_ge_ev_neg hx hC hC0 htneg
  obtain ⟨hev_lo, _⟩ := evTree_facts (vTree_eq hx hC hC0).2
  obtain ⟨htod_lo125, _⟩ := todTree_small hx hC hC0
  have hLHS : (0xde0b6b3a764000000000000000000000 : Int) * NUMv (vTree x) (int256 (tTree x)) -
      int256 (r0Tree x) * DENv (vTree x) (int256 (tTree x)) ≤
      2 ^ 637 * ((evTree x : Int) - int256 (todTree x)) +
        142941343449089 * 2 ^ 590 * (0xde0b6b3a764000000000000000000000 : Int) + 2 * 2 ^ 637 * (0xde0b6b3a764000000000000000000000 : Int) := by
    unfold NUMv DENv
    set r0 := int256 (r0Tree x) with hr0def
    set ev := (evTree x : Int) with hevdef
    set tod := int256 (todTree x) with htoddef
    set t := int256 (tTree x) with htdef
    set Ep := (evNumV (vTree x) : Int) with hEpdef
    set Op := (odNumV (vTree x) : Int) with hOpdef
    have hr0nn : (0:Int) ≤ r0 := by
      have : (0:Int) < 2 ^ 123 := by positivity
      linarith [hr0lo]
    have h2126r0_nn : (0:Int) ≤ (0xde0b6b3a764000000000000000000000 : Int) - r0 := by linarith [hr0le]
    have h2126r0_le : (0xde0b6b3a764000000000000000000000 : Int) - r0 ≤ (0xde0b6b3a764000000000000000000000 : Int) := by linarith [hr0nn]
    have hr0p_nn : (0:Int) ≤ (0xde0b6b3a764000000000000000000000 : Int) + r0 := by positivity
    have hr0p_le : (0xde0b6b3a764000000000000000000000 : Int) + r0 ≤ 2 * (0xde0b6b3a764000000000000000000000 : Int) := by linarith [hr0le]
    -- Ep·2^110·(2^126−r0) ≤ 2^637·ev·(2^126−r0) + Wev·2^590·2^126
    have hterm1 : Ep * 2 ^ 110 * ((0xde0b6b3a764000000000000000000000 : Int) - r0) ≤
        2 ^ 637 * ev * ((0xde0b6b3a764000000000000000000000 : Int) - r0) + 142941343449089 * 2 ^ 590 * (0xde0b6b3a764000000000000000000000 : Int) := by
      have h1 : Ep * 2 ^ 110 * ((0xde0b6b3a764000000000000000000000 : Int) - r0) ≤
          (2 ^ 637 * ev + 142941343449089 * 2 ^ 590) * ((0xde0b6b3a764000000000000000000000 : Int) - r0) := by
        apply mul_le_mul_of_nonneg_right _ h2126r0_nn
        nlinarith [hEp_hi]
      have h2 : (142941343449089 : Int) * 2 ^ 590 * ((0xde0b6b3a764000000000000000000000 : Int) - r0) ≤
          142941343449089 * 2 ^ 590 * (0xde0b6b3a764000000000000000000000 : Int) :=
        mul_le_mul_of_nonneg_left h2126r0_le (by positivity)
      nlinarith [h1, h2]
    -- t·Op·(2^126+r0) ≤ (2^637·tod + 2^637)·(2^126+r0) ≤ 2^637·tod·(2^126+r0) + 2·2^637·2^126
    have hterm2 : t * Op * ((0xde0b6b3a764000000000000000000000 : Int) + r0) ≤
        2 ^ 637 * tod * ((0xde0b6b3a764000000000000000000000 : Int) + r0) + 2 * 2 ^ 637 * (0xde0b6b3a764000000000000000000000 : Int) := by
      have h1 : t * Op * ((0xde0b6b3a764000000000000000000000 : Int) + r0) ≤ (2 ^ 637 * tod + 2 ^ 637) * ((0xde0b6b3a764000000000000000000000 : Int) + r0) :=
        mul_le_mul_of_nonneg_right htOp_hi hr0p_nn
      have h2 : (2:Int) ^ 637 * ((0xde0b6b3a764000000000000000000000 : Int) + r0) ≤ 2 ^ 637 * (2 * (0xde0b6b3a764000000000000000000000 : Int)) :=
        mul_le_mul_of_nonneg_left hr0p_le (by positivity)
      nlinarith [h1, h2]
    -- floor: 2^126·num − r0·den ≤ den, scaled
    have hfloor : (0xde0b6b3a764000000000000000000000 : Int) * (ev + tod) - r0 * (ev - tod) ≤ (ev - tod) := by
      linarith [hfloor_hi]
    have hfloor638 : (2:Int) ^ 637 * ((0xde0b6b3a764000000000000000000000 : Int) * (ev + tod) - r0 * (ev - tod)) ≤
        2 ^ 637 * (ev - tod) := mul_le_mul_of_nonneg_left hfloor (by positivity)
    nlinarith [hterm1, hterm2, hfloor638]
  -- budget against DENv ≥ 2^637·ev ≥ 2^637·A0; den ≤ ev + 2^125
  set ev := (evTree x : Int) with hevdef
  set tod := int256 (todTree x) with htoddef
  set D := DENv (vTree x) (int256 (tTree x)) with hDdef
  have hev : (207573926795459379279817565122117813128 : Int) ≤ ev := by
    have : (0x9c2948bcaca16a0dd2fe98bb4470c388 : Int) ≤ ev := by
      rw [hevdef]; exact_mod_cast hev_lo
    rw [show (0x9c2948bcaca16a0dd2fe98bb4470c388 : Int) = 207573926795459379279817565122117813128 from by norm_num] at this
    exact this
  have hden_le : ev - tod ≤ ev + 2 ^ 125 := by
    have : -(2 ^ 125 : Int) ≤ tod := htod_lo125
    linarith [this]
  have hDev : 2 ^ 637 * ev ≤ D := hDEN_ge
  -- 1000·(2^637·(ev + 2^125) + Wev·2^590·scaleQ68 + 2·2^637·scaleQ68) ≤ 1000·2^637·ev + 5210·2^637·A0
  have hlit : 1000 * (2 ^ 637 * 2 ^ 125 + 142941343449089 * 2 ^ 590 * (0xde0b6b3a764000000000000000000000 : Int) +
      2 * 2 ^ 637 * (0xde0b6b3a764000000000000000000000 : Int)) ≤
      (5210 : Int) * (2 ^ 637 * 207573926795459379279817565122117813128) := by
    norm_num
  have hAev : (5210 : Int) * (2 ^ 637 * 207573926795459379279817565122117813128) ≤ 5210 * D := by
    have h1 : (2:Int) ^ 637 * 207573926795459379279817565122117813128 ≤ 2 ^ 637 * ev :=
      mul_le_mul_of_nonneg_left hev (by positivity)
    have := le_trans h1 hDev
    nlinarith [this]
  nlinarith [hLHS, hden_le, hDev, hlit, hAev]

/-! ## The per-point deficit (nonneg half) -/

/-- **The per-point deficit (nonneg half).** `scaleQ68·exp(rt) ≤ r0 + 33/4`: link-1 `≤ 6210/1000`, the
`Mp` factor `≤ 2/25`, the under gap `≤ 1267/1000`; the granularity is free on this half. -/
theorem r0_real_under_tight {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    (0xde0b6b3a764000000000000000000000 : Real) * Real.exp (reducedArg x) ≤ (int256 (r0Tree x) : Real) + 33 / 4 := by
  obtain ⟨_, hthi⟩ := tTree_in_cert_domain hx hC hC0
  have hvle := vTree_le_vmax hx hC hC0
  set t := int256 (tTree x) with htdef
  set v := vTree x with hvdef
  set r0 := int256 (r0Tree x) with hr0def
  have htdom : t ≤ (ExpCertV.H128 : Int) := by
    rw [show ((ExpCertV.H128 : Nat) : Int) = 117932881612756647068972071382077242199 from by
      unfold ExpCertV.H128; norm_num]
    exact hthi
  have hD : 554482771859 * 2 ^ 725 ≤ DENv v t := DENv_ge_over (by omega) hthi
  have hDpos : (0:Int) < DENv v t := lt_of_lt_of_le (by positivity) hD
  have hDR : (0:Real) < (DENv v t : Real) := by exact_mod_cast hDpos
  have hDE : (1:Int) ≤ evalPoly ExpCertV.denExpV t := certDE_pos htnn htdom
  have hDER : (0:Real) < (evalPoly ExpCertV.denExpV t : Real) := by
    have : (0:Int) < evalPoly ExpCertV.denExpV t := lt_of_lt_of_le one_pos hDE
    exact_mod_cast this
  -- link 1: 2^126·Qv ≤ r0 + 6210/1000
  have hlink1 := link1_under_int hx hC hC0 htnn
  have hQv_le : (0xde0b6b3a764000000000000000000000 : Real) * ((NUMv v t : Real) / (DENv v t : Real)) ≤
      (r0 : Real) + 6210 / 1000 := by
    rw [mul_div_assoc', div_le_iff₀ hDR]
    have hR := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hlink1
    push_cast at hR
    nlinarith [hR, hDR]
  -- link 2 (free): NE/DE ≤ Qv
  obtain ⟨hgran1, _⟩ := gran_over_pair hx hC hC0 htnn
  -- link 3: Et ≤ (NE/DE)·Mpp ≤ Qv·Mpp; Mpp excess ≤ 2/25 via r0 ≤ 1.45·2^126
  have hcertup := certUp_real htnn htdom
  set Et := Real.exp ((t : Real) / (2 ^ 128 : Real)) with hEtdef
  set NE := evalPoly ExpCertV.numExpV t with hNEdef
  set DE := evalPoly ExpCertV.denExpV t with hDEdef
  set Mpp : Real := ((2 ^ 132 : Real) + 1) / (2 ^ 132 : Real) with hMppdef
  have hEt_le : Et ≤ ((NE : Real) / (DE : Real)) * Mpp := by
    have hc : Et ≤ ((2 ^ 132 + 1 : Int) : Real) * (NE : Real) /
        (((2 ^ 132 : Int) : Real) * (DE : Real)) := hcertup
    rw [hMppdef]
    have key : ((NE : Real) / (DE : Real)) * (((2 ^ 132 : Real) + 1) / (2 ^ 132 : Real)) =
        ((2 ^ 132 + 1 : Int) : Real) * (NE : Real) / (((2 ^ 132 : Int) : Real) * (DE : Real)) := by
      push_cast; field_simp; ring
    rw [key]; exact hc
  have hMpp_nn : (0:Real) ≤ Mpp := by rw [hMppdef]; positivity
  have hEt_le_Qv : Et ≤ ((NUMv v t : Real) / (DENv v t : Real)) * Mpp :=
    le_trans hEt_le (mul_le_mul_of_nonneg_right hgran1 hMpp_nn)
  have hMpp1 : Mpp - 1 = 1 / (2 ^ 132 : Real) := by rw [hMppdef]; field_simp
  obtain ⟨_, hr0hi145⟩ := r0_bracket_nonneg hx hC hC0 htnn
  have hr0R : (r0 : Real) ≤ (145 / 100) * (0xde0b6b3a764000000000000000000000 : Real) := by
    have h := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hr0hi145
    push_cast at h
    linarith [h]
  have hEt_bound : (0xde0b6b3a764000000000000000000000 : Real) * Et ≤ (r0 : Real) + 6210 / 1000 + 2 / 25 := by
    have h1 : (0xde0b6b3a764000000000000000000000 : Real) * Et ≤
        (0xde0b6b3a764000000000000000000000 : Real) * (((NUMv v t : Real) / (DENv v t : Real)) * Mpp) :=
      mul_le_mul_of_nonneg_left hEt_le_Qv (by positivity)
    have h2 : (0xde0b6b3a764000000000000000000000 : Real) * (((NUMv v t : Real) / (DENv v t : Real)) * Mpp) =
        (0xde0b6b3a764000000000000000000000 : Real) * ((NUMv v t : Real) / (DENv v t : Real)) +
          ((0xde0b6b3a764000000000000000000000 : Real) * ((NUMv v t : Real) / (DENv v t : Real))) * (Mpp - 1) := by ring
    have h3 : ((0xde0b6b3a764000000000000000000000 : Real) * ((NUMv v t : Real) / (DENv v t : Real))) * (Mpp - 1) ≤ 2 / 25 := by
      rw [hMpp1]
      have hcap : (0xde0b6b3a764000000000000000000000 : Real) * ((NUMv v t : Real) / (DENv v t : Real)) ≤
          (145 / 100) * (0xde0b6b3a764000000000000000000000 : Real) + 6210 / 1000 := by linarith [hQv_le, hr0R]
      have := mul_le_mul_of_nonneg_right hcap (by positivity : (0:Real) ≤ 1 / (2 ^ 132 : Real))
      have hfin : ((145 / 100) * (0xde0b6b3a764000000000000000000000 : Real) + 6210 / 1000) * (1 / (2 ^ 132 : Real)) ≤
          2 / 25 := by norm_num
      linarith [this, hfin]
    linarith [h1, h2 ▸ h1, h3, hQv_le]
  -- link 4 (under gap): 2^126·(Ert − Et) ≤ 1267/1000
  set Ert := Real.exp (reducedArg x) with hErtdef
  have hgapunder := reducedArg_close_under hx hC hC0
  have hExp_diff : Ert - Et ≤ (reducedArg x - (t : Real) / (2 ^ 128 : Real)) * Ert := exp_diff_le _ _
  have hErt_le := exp_reducedArg_le_sqrt2bound hx hC hC0
  rw [← hErtdef] at hErt_le
  have hErt_nn : (0:Real) ≤ Ert := le_of_lt (Real.exp_pos _)
  have hgap126 : (0xde0b6b3a764000000000000000000000 : Real) * (Ert - Et) ≤ 1267 / 1000 := by
    have hgap : Ert - Et ≤ (33 / (32 * (2 ^ 128 : Real))) * Ert :=
      le_trans hExp_diff (mul_le_mul_of_nonneg_right (le_of_lt hgapunder) hErt_nn)
    have h1 : (0xde0b6b3a764000000000000000000000 : Real) * (Ert - Et) ≤ (0xde0b6b3a764000000000000000000000 : Real) * ((33 / (32 * (2 ^ 128 : Real))) * Ert) :=
      mul_le_mul_of_nonneg_left hgap (by positivity)
    have h2 : (0xde0b6b3a764000000000000000000000 : Real) * ((33 / (32 * (2 ^ 128 : Real))) * Ert) ≤
        (0xde0b6b3a764000000000000000000000 : Real) * ((33 / (32 * (2 ^ 128 : Real))) * (14143 / 10000)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hErt_le (by positivity)) (by positivity)
    have h3 : (0xde0b6b3a764000000000000000000000 : Real) * ((33 / (32 * (2 ^ 128 : Real))) * (14143 / 10000)) ≤ 1267 / 1000 := by
      norm_num
    linarith [h1, h2, h3]
  have hdist : (0xde0b6b3a764000000000000000000000 : Real) * Ert = (0xde0b6b3a764000000000000000000000 : Real) * Et + (0xde0b6b3a764000000000000000000000 : Real) * (Ert - Et) := by
    ring
  show (0xde0b6b3a764000000000000000000000 : Real) * Ert ≤ (r0 : Real) + 33 / 4
  have hsum : (6210 : Real) / 1000 + 2 / 25 + 1267 / 1000 ≤ 33 / 4 := by norm_num
  linarith [hEt_bound, hgap126, hdist, hsum]

/-! ## The per-point deficit (nonpositive half) -/

/-- **The per-point deficit (nonpositive half).** `scaleQ68·exp(rt) ≤ r0 + 33/4`: link-1 `≤ 6210/1000`,
the `Mp`-folded granularity `≤ (5¹⁸/2⁴⁰)·1644901622230542074/10¹⁹`, the `Mp` factor `≤ 2/25`
(via `r0 ≤ scaleQ68`), the under gap `≤ 1267/1000`. -/
theorem r0_real_under_tight_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) :
    (0xde0b6b3a764000000000000000000000 : Real) * Real.exp (reducedArg x) ≤ (int256 (r0Tree x) : Real) + 33 / 4 := by
  have htdom := tdom_neg hx hC hC0 htneg
  have hvle := vTree_le_vmax hx hC hC0
  set t := int256 (tTree x) with htdef
  set v := vTree x with hvdef
  set r0 := int256 (r0Tree x) with hr0def
  have hD : 554482771859 * 2 ^ 725 ≤ DENv v t := DENv_ge_neg (by omega) htneg
  have hDpos : (0:Int) < DENv v t := lt_of_lt_of_le (by positivity) hD
  have hDR : (0:Real) < (DENv v t : Real) := by exact_mod_cast hDpos
  have hDEpos : (0:Int) < evalPoly ExpCertV.denExpV t := (certNE_pos_neg_aux htneg htdom).2
  have hDER : (0:Real) < (evalPoly ExpCertV.denExpV t : Real) := by exact_mod_cast hDEpos
  -- link 1: 2^126·Qv ≤ r0 + 6210/1000
  have hlink1 := link1_under_int_neg hx hC hC0 htneg
  have hQv_le : (0xde0b6b3a764000000000000000000000 : Real) * ((NUMv v t : Real) / (DENv v t : Real)) ≤
      (r0 : Real) + 6210 / 1000 := by
    rw [mul_div_assoc', div_le_iff₀ hDR]
    have hR := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hlink1
    push_cast at hR
    nlinarith [hR, hDR]
  -- links 2+3: Et ≤ (NE/DE)·Mp = Qv·Mp + (NE/DE − Qv)·Mp
  have hcertup := certUp_real_neg htneg htdom
  set Et := Real.exp ((t : Real) / (2 ^ 128 : Real)) with hEtdef
  set NE := evalPoly ExpCertV.numExpV t with hNEdef
  set DE := evalPoly ExpCertV.denExpV t with hDEdef
  set Mp : Real := (2 ^ 132 : Real) / ((2 ^ 132 : Real) - 1) with hMpdef
  have hEt_le : Et ≤ ((NE : Real) / (DE : Real)) * Mp := by
    rw [hMpdef]
    have key : ((NE : Real) / (DE : Real)) * ((2 ^ 132 : Real) / ((2 ^ 132 : Real) - 1)) =
        ((2 ^ 132 : Int) : Real) * (NE : Real) /
          (((2 ^ 132 - 1 : Int) : Real) * (DE : Real)) := by
      push_cast; field_simp; ring
    rw [key]; exact hcertup
  obtain ⟨_, hgran2⟩ := gran_under_pair hx hC hC0 htneg
  have hMp_nn : (0:Real) ≤ Mp := by
    rw [hMpdef]
    have : (0:Real) < (2 ^ 132 : Real) - 1 := by norm_num
    positivity
  have hMp1 : Mp - 1 = 1 / ((2 ^ 132 : Real) - 1) := by rw [hMpdef]; field_simp
  have hr0le := r0_le_scale_neg hx hC hC0 htneg
  have hr0R : (r0 : Real) ≤ (0xde0b6b3a764000000000000000000000 : Real) := by
    have h := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hr0le
    push_cast at h
    linarith [h]
  have hEt_bound : (0xde0b6b3a764000000000000000000000 : Real) * Et ≤ (r0 : Real) + 6210 / 1000 + 2 / 25 +
      3814697265625 * 1644901622230542074 / (10000000000000000000 * 1099511627776) := by
    have h1 : (0xde0b6b3a764000000000000000000000 : Real) * Et ≤ (0xde0b6b3a764000000000000000000000 : Real) * (((NE : Real) / (DE : Real)) * Mp) :=
      mul_le_mul_of_nonneg_left hEt_le (by positivity)
    -- split: 2^126·(NE/DE)·Mp = 2^126·Qv + 2^126·Qv·(Mp−1) + 2^126·Mp·(NE/DE − Qv)
    have hsplit : (0xde0b6b3a764000000000000000000000 : Real) * (((NE : Real) / (DE : Real)) * Mp) =
        (0xde0b6b3a764000000000000000000000 : Real) * ((NUMv v t : Real) / (DENv v t : Real)) +
        ((0xde0b6b3a764000000000000000000000 : Real) * ((NUMv v t : Real) / (DENv v t : Real))) * (Mp - 1) +
        (0xde0b6b3a764000000000000000000000 : Real) * Mp *
          ((NE : Real) / (DE : Real) - (NUMv v t : Real) / (DENv v t : Real)) := by ring
    have hMpterm : ((0xde0b6b3a764000000000000000000000 : Real) * ((NUMv v t : Real) / (DENv v t : Real))) * (Mp - 1) ≤
        2 / 25 := by
      rw [hMp1]
      have hcap : (0xde0b6b3a764000000000000000000000 : Real) * ((NUMv v t : Real) / (DENv v t : Real)) ≤
          (0xde0b6b3a764000000000000000000000 : Real) + 6210 / 1000 := by linarith [hQv_le, hr0R]
      have := mul_le_mul_of_nonneg_right hcap
        (by positivity : (0:Real) ≤ 1 / ((2 ^ 132 : Real) - 1))
      have hfin : ((0xde0b6b3a764000000000000000000000 : Real) + 6210 / 1000) * (1 / ((2 ^ 132 : Real) - 1)) ≤ 2 / 25 := by
        rw [mul_one_div, div_le_div_iff₀ (by norm_num) (by norm_num)]
        norm_num
      linarith [this, hfin]
    linarith [h1, hsplit ▸ h1, hMpterm, hgran2, hQv_le]
  -- link 4 (under gap): 2^126·(Ert − Et) ≤ 1267/1000
  set Ert := Real.exp (reducedArg x) with hErtdef
  have hgapunder := reducedArg_close_under hx hC hC0
  have hExp_diff : Ert - Et ≤ (reducedArg x - (t : Real) / (2 ^ 128 : Real)) * Ert := exp_diff_le _ _
  have hErt_le := exp_reducedArg_le_sqrt2bound hx hC hC0
  rw [← hErtdef] at hErt_le
  have hErt_nn : (0:Real) ≤ Ert := le_of_lt (Real.exp_pos _)
  have hgap126 : (0xde0b6b3a764000000000000000000000 : Real) * (Ert - Et) ≤ 1267 / 1000 := by
    have hgap : Ert - Et ≤ (33 / (32 * (2 ^ 128 : Real))) * Ert :=
      le_trans hExp_diff (mul_le_mul_of_nonneg_right (le_of_lt hgapunder) hErt_nn)
    have h1 : (0xde0b6b3a764000000000000000000000 : Real) * (Ert - Et) ≤ (0xde0b6b3a764000000000000000000000 : Real) * ((33 / (32 * (2 ^ 128 : Real))) * Ert) :=
      mul_le_mul_of_nonneg_left hgap (by positivity)
    have h2 : (0xde0b6b3a764000000000000000000000 : Real) * ((33 / (32 * (2 ^ 128 : Real))) * Ert) ≤
        (0xde0b6b3a764000000000000000000000 : Real) * ((33 / (32 * (2 ^ 128 : Real))) * (14143 / 10000)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hErt_le (by positivity)) (by positivity)
    have h3 : (0xde0b6b3a764000000000000000000000 : Real) * ((33 / (32 * (2 ^ 128 : Real))) * (14143 / 10000)) ≤ 1267 / 1000 := by
      norm_num
    linarith [h1, h2, h3]
  have hdist : (0xde0b6b3a764000000000000000000000 : Real) * Ert = (0xde0b6b3a764000000000000000000000 : Real) * Et + (0xde0b6b3a764000000000000000000000 : Real) * (Ert - Et) := by
    ring
  show (0xde0b6b3a764000000000000000000000 : Real) * Ert ≤ (r0 : Real) + 33 / 4
  have hsum : (6210 : Real) / 1000 + 2 / 25 + 3814697265625 * 1644901622230542074 / (10000000000000000000 * 1099511627776) +
      1267 / 1000 ≤ 33 / 4 := by norm_num
  linarith [hEt_bound, hgap126, hdist, hsum]

/-- **Per-point deficit (tight, any sign):** `scaleQ68·exp(rt) ≤ r0 + 33/4`. -/
theorem r0_real_under_within {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (0xde0b6b3a764000000000000000000000 : Real) * Real.exp (reducedArg x) ≤ (int256 (r0Tree x) : Real) + 33 / 4 := by
  rcases le_or_gt 0 (int256 (tTree x)) with htnn | htneg
  · exact r0_real_under_tight hx hC hC0 htnn
  · exact r0_real_under_tight_neg hx hC hC0 (le_of_lt htneg)

/-! ## The octave-seam `r0`-doubling consequence -/

/-- `2¹²⁶ < r0Tree x` on the region (`r0 ≥ scaleQ68·exp(rt) − 33/4 > scaleQ68/2 − 33/4 > 2¹²⁶`). -/
theorem r0Tree_gt_2126 {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (2 : Real) ^ 126 < (int256 (r0Tree x) : Real) := by
  have hu := r0_real_under_within hx hC hC0
  have hh := exp_reducedArg_gt_half hx hC hC0
  have h1 : (0xde0b6b3a764000000000000000000000 : Real) * (1 / 2) < (0xde0b6b3a764000000000000000000000 : Real) * Real.exp (reducedArg x) :=
    mul_lt_mul_of_pos_left hh (by positivity)
  have h2 : (2 : Real) ^ 126 + (33 / 4 : Real) < (0xde0b6b3a764000000000000000000000 : Real) * (1 / 2) := by norm_num
  linarith [hu, h1, h2]

/-- **The seam exp relation.** Across a seam (`X2 = X1 + 1`, `k2 = k1 + 1`),
`exp(rt1) = 2·exp(rt2)·exp(−1/RAY)`. -/
theorem reducedArg_seam {x1 x2 : Nat}
    (hk : int256 (kTree x2) = int256 (kTree x1) + 1)
    (hadj : int256 x2 = int256 x1 + 1) :
    Real.exp (reducedArg x1) =
      2 * Real.exp (reducedArg x2) * Real.exp (-(1 / (10 ^ 27 : Real))) := by
  have hrel : reducedArg x1 = reducedArg x2 + Real.log 2 + (-(1 / (10 ^ 27 : Real))) := by
    unfold reducedArg
    rw [show (int256 x2 : Real) = (int256 x1 : Real) + 1 from by exact_mod_cast hadj,
      show (int256 (kTree x2) : Real) = (int256 (kTree x1) : Real) + 1 from by exact_mod_cast hk]
    ring
  rw [hrel, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0:Real) < 2)]
  ring

/-- **`r0` at most doubles across a seam, three units short** (the real reduction of
`SeamR0Bound`). The strict slack from `exp(−1/RAY) < 1` (against `r0Tree x2 > 2¹²⁶`, worth
`≈ 8.5·10¹⁰` grid units) dwarfs the per-point envelopes and the three integer units the
seam-floor comparison consumes. -/
theorem r0_seam_double {x1 x2 : Nat}
    (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hC1 : int256 Cmask < int256 x1) (hC01 : int256 x1 < int256 C0thresh)
    (hC2 : int256 Cmask < int256 x2) (hC02 : int256 x2 < int256 C0thresh)
    (hk : int256 (kTree x2) = int256 (kTree x1) + 1)
    (hadj : int256 x2 = int256 x1 + 1) :
    int256 (r0Tree x1) + 3 ≤ 2 * int256 (r0Tree x2) := by
  have hover1 := r0_real_over_within hx1 hC1 hC01
  have hunder2 := r0_real_under_within hx2 hC2 hC02
  have hr0_2_big := r0Tree_gt_2126 hx2 hC2 hC02
  have hseam := reducedArg_seam hk hadj
  set E1 := Real.exp (reducedArg x1) with hE1
  set E2 := Real.exp (reducedArg x2) with hE2
  set y := Real.exp (-(1 / (10 ^ 27 : Real))) with hy
  have hy_pos : 0 < y := Real.exp_pos _
  -- y ≤ 1 - 1/(2·RAY)
  have hy_bound : y ≤ 1 - 1 / (2 * (10 ^ 27 : Real)) := by
    rw [hy]
    have hz : (0:Real) < 1 / (10 ^ 27 : Real) := by positivity
    have hez : (1 : Real) + 1 / (10 ^ 27 : Real) ≤ Real.exp (1 / (10 ^ 27 : Real)) := by
      have := Real.add_one_le_exp (1 / (10 ^ 27 : Real)); linarith [this]
    rw [Real.exp_neg]
    have hexppos : 0 < Real.exp (1 / (10 ^ 27 : Real)) := Real.exp_pos _
    rw [inv_le_iff_one_le_mul₀ hexppos]
    have h1z : (1 - 1 / (2 * (10 ^ 27 : Real))) * (1 + 1 / (10 ^ 27 : Real)) ≥ 1 := by
      rw [ge_iff_le]; nlinarith [sq_nonneg (1 / (10 ^ 27 : Real))]
    nlinarith [hez, h1z, hexppos, mul_pos (by positivity : (0:Real) < 1 - 1/(2*(10^27:Real))) hexppos]
  -- scaleQ68·E1 = 2·(scaleQ68·E2)·y ≤ 2·(r0_2 + U)·y
  have hE2bound : (0xde0b6b3a764000000000000000000000 : Real) * E2 ≤ (int256 (r0Tree x2) : Real) + (33 / 4 : Real) :=
    hunder2
  have hr0_1 : (int256 (r0Tree x1) : Real) ≤
      2 * ((int256 (r0Tree x2) : Real) + (33 / 4 : Real)) * y +
        3814697265625 * 5792534503673398887 / (10000000000000000000 * 1099511627776) := by
    have h1 : (0xde0b6b3a764000000000000000000000 : Real) * E1 = 2 * ((0xde0b6b3a764000000000000000000000 : Real) * E2) * y := by
      rw [hseam]; ring
    have h2 : (int256 (r0Tree x1) : Real) ≤ (0xde0b6b3a764000000000000000000000 : Real) * E1 +
        3814697265625 * 5792534503673398887 / (10000000000000000000 * 1099511627776) := hover1
    rw [h1] at h2
    have h3 : 2 * ((0xde0b6b3a764000000000000000000000 : Real) * E2) * y ≤
        2 * ((int256 (r0Tree x2) : Real) + (33 / 4 : Real)) * y :=
      mul_le_mul_of_nonneg_right
        (by linarith [mul_le_mul_of_nonneg_left hE2bound (by norm_num : (0:Real) ≤ 2)])
        (le_of_lt hy_pos)
    linarith [h2, h3]
  have hr0_2nn : (0:Real) ≤ (int256 (r0Tree x2) : Real) := by
    linarith [hr0_2_big, (by positivity : (0:Real) ≤ (2:Real)^126)]
  have hkey : 2 * ((int256 (r0Tree x2) : Real) + (33 / 4 : Real)) * y +
      3814697265625 * 5792534503673398887 / (10000000000000000000 * 1099511627776) + 3 < 2 * (int256 (r0Tree x2) : Real) := by
    -- the seam gap is dominated by `(r0 + U) / RAY`; the quotient exceeds `8.5·10¹⁰` here
    have hyb : 2 * ((int256 (r0Tree x2) : Real) + (33 / 4 : Real)) * y ≤
        2 * ((int256 (r0Tree x2) : Real) + (33 / 4 : Real)) * (1 - 1 / (2 * (10 ^ 27 : Real))) := by
      apply mul_le_mul_of_nonneg_left hy_bound
      linarith [hr0_2nn]
    have hexpand : 2 * ((int256 (r0Tree x2) : Real) + (33 / 4 : Real)) *
          (1 - 1 / (2 * (10 ^ 27 : Real))) =
        2 * (int256 (r0Tree x2) : Real) + 2 * (33 / 4 : Real) -
          ((int256 (r0Tree x2) : Real) + (33 / 4 : Real)) / (10 ^ 27 : Real) := by
      field_simp
      ring
    have hbig : ((int256 (r0Tree x2) : Real) + (33 / 4 : Real)) / (10 ^ 27 : Real) > 30 := by
      rw [gt_iff_lt, lt_div_iff₀ (by positivity)]
      nlinarith [hr0_2_big, (by norm_num : (30:Real) * 10 ^ 27 + 1 < 2 ^ 126)]
    have hUB : 2 * (33 / 4 : Real) + 3814697265625 * 5792534503673398887 / (10000000000000000000 * 1099511627776) + 3 < 30 := by norm_num
    linarith [hyb, hexpand ▸ hyb, hbig, hUB]
  have hreal : (int256 (r0Tree x1) : Real) + 3 ≤ 2 * (int256 (r0Tree x2) : Real) := by
    linarith [hr0_1, hkey]
  have hcast : ((int256 (r0Tree x1) + 3 : Int) : Real) ≤ ((2 * int256 (r0Tree x2) : Int) : Real) := by
    push_cast
    linarith [hreal]
  exact_mod_cast hcast

end

end ExpYul
