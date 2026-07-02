import ExpProof.Floor.GranPair
import ExpProof.Floor.Reduce
import ExpProof.Mono.Quot
import ExpProof.Mono.Cross
import Common.Seam.RealExpBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The per-point `r0`-vs-`exp` bridge (never-over side)

This module bounds the Q126 quotient `r0Tree x` above by `2¹²⁶·exp(rt)` plus the never-over budget
(`rt = X/RAY − k·ln2` the reduced argument), the analytic content the floor brackets
(`Floor.R0BoundHolds`) consume. The chain has four links:

1. **`r0` vs `ê(v)`** — Horner stage truncation and the closing `div` floor only: the runtime
   accumulators bracket the exact integer polynomials (`evTree_bracket`/`odTree_bracket`), and the
   shared even truncation cancels through the floor, leaving the jitter
   `≤ 6207065162659510332/10¹⁹`;
2. **`ê(v)` vs `ê(t²)`** — the argument-granularity link (`Floor.GranV`): one `v`-grid grain,
   `≤ 3290521163436398582/10¹⁹` on this half (the 32-piece certified envelope);
3. **`ê(t²)` vs `exp(t/2¹²⁸)`** — the `2⁻¹³¹`-nudged Taylor cut (`Floor.CapsV`), the `Mp` factor
   `≤ 441941738241592203/10¹⁹`;
4. **`exp(t/2¹²⁸)` vs `exp(rt)`** — the reduced-argument gap (`Floor.Reduce`),
   `≤ 110485434560398051/10¹⁹`.

The total is the budget `B = 10050013498897899168/10¹⁹`; `MARGIN = ⌊5¹⁸·B⌋ + 1`. On the `t ≤ 0`
half link 2 is free (the grain moves `ê` the other way) and links 3–4 shrink (`ê ≤ 1`), so the same
`B` covers both halves.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Poly

set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 2000

/-! ## The `div` floor sandwich -/

/-- The Q126 quotient is the integer floor: `r0·den_rt ≤ 2¹²⁶·num_rt < (r0+1)·den_rt` with
`num_rt = ev + tod`, `den_rt = ev − tod`. -/
theorem r0_floor_sandwich {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    int256 (r0Tree x) * ((evTree x : Int) - int256 (todTree x)) ≤
        2 ^ 126 * ((evTree x : Int) + int256 (todTree x)) ∧
      2 ^ 126 * ((evTree x : Int) + int256 (todTree x)) <
        (int256 (r0Tree x) + 1) * ((evTree x : Int) - int256 (todTree x)) := by
  obtain ⟨hadd, hsub, hnum_pos, hden_pos⟩ := numden_pos hx hC hC0
  obtain ⟨hr0lo, hr0hi⟩ := r0Tree_bounds hx hC hC0
  set num := evmAdd (evTree x) (todTree x) with hnumdef
  set den := evmSub (evTree x) (todTree x) with hdendef
  have hnumw : num < 2 ^ 256 := evmAdd_lt _ _
  have hdenw : den < 2 ^ 256 := evmSub_lt _ _
  -- num, den are below 2^128 (signed = Nat value)
  have hnumi : int256 num = (evTree x : Int) + int256 (todTree x) := hadd
  have hdeni : int256 den = (evTree x : Int) - int256 (todTree x) := hsub
  -- num < 2^128, den < 2^128
  obtain ⟨hnumeq, hnum255⟩ := int256_eq_of_nonneg hnumw (by rw [hnumi]; omega)
  obtain ⟨hdeneq, hden255⟩ := int256_eq_of_nonneg hdenw (by rw [hdeni]; omega)
  -- the shl: int256 (shl 126 num) = 2^126·int256 num
  have hnumlt128 : int256 num < 2 ^ 128 := by
    -- num = ev + tod < 2^127 + 2^125 < 2^128
    obtain ⟨_, hevhi⟩ := evTree_facts (vTree_eq hx hC hC0).2
    obtain ⟨_, htod_hi, _, _⟩ := todTree_bound hx hC hC0
    rw [hnumi]
    have : (evTree x : Int) < 2 ^ 127 := by exact_mod_cast hevhi
    have ht125 : int256 (todTree x) < 2 ^ 125 := htod_hi
    nlinarith [this, ht125]
  have hshl : int256 (evmShl 0x7e num) = 2 ^ 0x7e * int256 num :=
    shl126_transport hnumw (by rw [hnumi]; omega) hnumlt128
  -- r0 = div (shl 126 num) den, with both operands positive
  have hr0eq : r0Tree x = evmDiv (evmShl 0x7e num) den := rfl
  have hshlw : evmShl 0x7e num < 2 ^ 256 := evmShl_lt _ _
  have hshlpos : 0 ≤ int256 (evmShl 0x7e num) := by rw [hshl, hnumi]; positivity
  have hdenpos' : 0 < int256 den := by rw [hdeni]; omega
  have hdiv := evmDiv_pos_pos hshlw hdenw hshlpos hdenpos'
  rw [← hr0eq] at hdiv
  -- toNat values
  have hshl_toNat : (int256 (evmShl 0x7e num)).toNat = (evmShl 0x7e num) := by
    have h := int256_eq_of_nonneg hshlw hshlpos
    rw [h.1, Int.toNat_natCast]
  have hden_toNat : (int256 den).toNat = den := by rw [hdeneq, Int.toNat_natCast]
  rw [hshl_toNat, hden_toNat] at hdiv
  -- the Nat floor: r0 = (shl 126 num) / den
  have hnumnat128 : num < 2 ^ 128 := by
    have hh : ((num : Nat) : Int) < 2 ^ 128 := by rw [hnumeq] at hnumlt128; exact hnumlt128
    exact_mod_cast hh
  have hshlval : evmShl 0x7e num = num * 2 ^ 0x7e := by
    refine evmShl_eq (by norm_num) ?_
    calc num * 2 ^ 0x7e < 2 ^ 128 * 2 ^ 0x7e := (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hnumnat128
      _ = 2 ^ 254 := by rw [← Nat.pow_add]
      _ < 2 ^ 256 := by norm_num
  -- Nat floor sandwich on the opaque dividend M := num·2^126
  have hdennat : 0 < den := by
    have hh : (0:Int) < (den:Int) := by rw [hdeneq] at hdenpos'; exact hdenpos'
    exact_mod_cast hh
  rw [hshlval] at hdiv
  set M := num * 2 ^ 0x7e with hMdef
  set q := M / den with hqdef
  have hfloor_lo : q * den ≤ M := Nat.div_mul_le_self _ _
  have hfloor_hi : M < (q + 1) * den := by
    have hdm : den * q + M % den = M := Nat.div_add_mod M den
    have hmod : M % den < den := Nat.mod_lt M hdennat
    calc M = den * q + M % den := hdm.symm
      _ < den * q + den := Nat.add_lt_add_left hmod _
      _ = (q + 1) * den := by ring
  -- transport to Int with the canonical values
  have hr0nat : int256 (r0Tree x) = (q : Int) := hdiv
  -- canonical: (num:Int) = ev + tod, (den:Int) = ev - tod
  have hgoalnum : (evTree x : Int) + int256 (todTree x) = (num : Int) := by rw [← hnumi, hnumeq]
  have hgoalden : (evTree x : Int) - int256 (todTree x) = (den : Int) := by rw [← hdeni, hdeneq]
  rw [hr0nat, hgoalnum, hgoalden]
  have heM : (M : Int) = 2 ^ 126 * (num : Int) := by rw [hMdef]; push_cast; ring
  constructor
  · have h : (q * den : Nat) ≤ M := hfloor_lo
    have hInt : (q : Int) * (den : Int) ≤ (M : Int) := by exact_mod_cast h
    rw [heM] at hInt; linarith [hInt]
  · have h : M < ((q + 1) * den : Nat) := hfloor_hi
    have hInt : (M : Int) < ((q : Int) + 1) * (den : Int) := by exact_mod_cast h
    rw [heM] at hInt; linarith [hInt]

/-- `den_rt = ev − tod ≥ 0.72·2¹²⁶` on the region (the even accumulator dominates `|tod|`). -/
theorem den_ge_072 {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (61251667532612381706986956632087880162 : Int) ≤
      (evTree x : Int) - int256 (todTree x) := by
  obtain ⟨hevlo, _⟩ := evTree_facts (vTree_eq hx hC hC0).2
  obtain ⟨_, htod_hi, _, _⟩ := todTree_bound hx hC hC0
  have hev : (0x4e14a45e5650b506e97f4c5da23861e2 : Int) ≤ (evTree x : Int) := by exact_mod_cast hevlo
  have ht125 : int256 (todTree x) < 2 ^ 125 := htod_hi
  rw [show (0x4e14a45e5650b506e97f4c5da23861e2 : Int) = 103786963397729689639908782561058906594 from by norm_num] at hev
  rw [show (2:Int)^125 = 42535295865117307932921825928971026432 from by norm_num] at ht125
  omega

/-- On the nonpositive half `tod ≤ 0` and hence `r0 ≤ 2¹²⁶` (num ≤ den). -/
theorem r0_le_2126_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) :
    int256 (r0Tree x) ≤ 2 ^ 126 := by
  obtain ⟨hfloor_lo, _⟩ := r0_floor_sandwich hx hC hC0
  set r0 := int256 (r0Tree x) with hr0def
  set ev := (evTree x : Int) with hevdef
  set tod := int256 (todTree x) with htoddef
  have hden072 : (61251667532612381706986956632087880162 : Int) ≤ ev - tod := by
    have := den_ge_072 hx hC hC0; rw [← hevdef, ← htoddef] at this; exact this
  have hdenpos : (0:Int) < ev - tod := lt_of_lt_of_le (by norm_num) hden072
  have htodnp : tod ≤ 0 := by
    obtain ⟨_, _, htodlo, _⟩ := todTree_bound hx hC hC0
    have hodnn : (0:Int) ≤ (odTree x : Int) := Int.natCast_nonneg _
    have : int256 (tTree x) * (odTree x : Int) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg htneg hodnn
    nlinarith [htodlo, this]
  -- r0·den ≤ 2^126·num ≤ 2^126·den (num ≤ den)
  have hnumden : r0 * (ev - tod) ≤ 2 ^ 126 * (ev - tod) := by
    have h1 : r0 * (ev - tod) ≤ 2 ^ 126 * (ev + tod) := hfloor_lo
    nlinarith [h1, htodnp, (by positivity : (0:Int) ≤ (2:Int)^126)]
  exact le_of_mul_le_mul_right hnumden hdenpos

/-! ## The runtime brackets lifted to the `2^725` alignment

`NUMv/DENv = Ev·2^110 ± t·Od` (`Floor.GranV`). The Horner-truncation brackets
(`evTree_bracket`/`odTree_bracket`, widths `Wev = 283678831804417·2^480 ≈ 1.0079·2^528` and
`Wod = 1075052609·2^480 ≈ 1.0013·2^510`) and the `tod` floor (`todTree_bound`) tie them to the
runtime `ev`/`tod` at the common scale `2^638`. -/

/-- The `Int`-cast Horner brackets and `tod` floor collected. -/
theorem bridge_facts {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    2 ^ 528 * (evTree x : Int) ≤ (evNumV (vTree x) : Int) ∧
      (evNumV (vTree x) : Int) < 2 ^ 528 * (evTree x : Int) + 283678831804417 * 2 ^ 480 ∧
      2 ^ 510 * (odTree x : Int) ≤ (odNumV (vTree x) : Int) ∧
      (odNumV (vTree x) : Int) < 2 ^ 510 * (odTree x : Int) + 1075052609 * 2 ^ 480 := by
  obtain ⟨_, hvlt⟩ := vTree_eq hx hC hC0
  obtain ⟨hev_lo, hev_hi⟩ := evTree_bracket hvlt
  obtain ⟨hod_lo, hod_hi⟩ := odTree_bracket hvlt
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast hev_lo
  · exact_mod_cast hev_hi
  · exact_mod_cast hod_lo
  · exact_mod_cast hod_hi

/-- The `t·Od` product brackets (nonnegative half): `2⁶³⁸·tod ≤ t·Od` and
`t·Od ≤ 2⁶³⁸·tod + 2⁶³⁸ + Wod·2⁴⁸⁰·t`. -/
theorem tOd_bracket_nonneg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    2 ^ 638 * int256 (todTree x) ≤ int256 (tTree x) * (odNumV (vTree x) : Int) ∧
      int256 (tTree x) * (odNumV (vTree x) : Int) ≤
        2 ^ 638 * int256 (todTree x) + 2 ^ 638 + 1075052609 * 2 ^ 480 * int256 (tTree x) := by
  obtain ⟨_, _, hOp_lo, hOp_hi⟩ := bridge_facts hx hC hC0
  obtain ⟨_, _, htod_lo, htod_hi⟩ := todTree_bound hx hC hC0
  set t := int256 (tTree x) with htdef
  set od := (odTree x : Int) with hoddef
  set tod := int256 (todTree x) with htoddef
  set Op := (odNumV (vTree x) : Int) with hOpdef
  constructor
  · -- t·Op ≥ t·(2^510·od) = 2^510·(t·od) ≥ 2^510·(2^128·tod) = 2^638·tod
    have h1 : t * (2 ^ 510 * od) ≤ t * Op := mul_le_mul_of_nonneg_left hOp_lo htnn
    have h2 : (2:Int) ^ 510 * (2 ^ 128 * tod) ≤ 2 ^ 510 * (t * od) :=
      mul_le_mul_of_nonneg_left htod_lo (by positivity)
    nlinarith [h1, h2]
  · -- t·Op ≤ t·(2^510·od + Wod·2^480) ≤ 2^510·(2^128·tod + 2^128) + Wod·2^480·t
    have h1 : t * Op ≤ t * (2 ^ 510 * od + 1075052609 * 2 ^ 480) :=
      mul_le_mul_of_nonneg_left (le_of_lt hOp_hi) htnn
    have h2 : (2:Int) ^ 510 * (t * od) ≤ 2 ^ 510 * (2 ^ 128 * tod + 2 ^ 128) :=
      mul_le_mul_of_nonneg_left (le_of_lt htod_hi) (by positivity)
    nlinarith [h1, h2]

/-- The `t·Od` product brackets (nonpositive half): `t·Od ≤ 2⁶³⁸·tod + 2⁶³⁸` and
`2⁶³⁸·tod − Wod·2⁴⁸⁰·(−t) ≤ t·Od`. -/
theorem tOd_bracket_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) :
    int256 (tTree x) * (odNumV (vTree x) : Int) ≤ 2 ^ 638 * int256 (todTree x) + 2 ^ 638 ∧
      2 ^ 638 * int256 (todTree x) - 1075052609 * 2 ^ 480 * (-(int256 (tTree x))) ≤
        int256 (tTree x) * (odNumV (vTree x) : Int) := by
  obtain ⟨_, _, hOp_lo, hOp_hi⟩ := bridge_facts hx hC hC0
  obtain ⟨_, _, htod_lo, htod_hi⟩ := todTree_bound hx hC hC0
  set t := int256 (tTree x) with htdef
  set od := (odTree x : Int) with hoddef
  set tod := int256 (todTree x) with htoddef
  set Op := (odNumV (vTree x) : Int) with hOpdef
  constructor
  · -- t·Op ≤ t·(2^510·od) = 2^510·(t·od) ≤ 2^510·(2^128·tod + 2^128)
    have h1 : t * Op ≤ t * (2 ^ 510 * od) := mul_le_mul_of_nonpos_left hOp_lo htneg
    have h2 : (2:Int) ^ 510 * (t * od) ≤ 2 ^ 510 * (2 ^ 128 * tod + 2 ^ 128) :=
      mul_le_mul_of_nonneg_left (le_of_lt htod_hi) (by positivity)
    nlinarith [h1, h2]
  · -- t·Op ≥ t·(2^510·od + Wod·2^480) = 2^510·(t·od) + Wod·2^480·t ≥ 2^638·tod − Wod·2^480·(−t)
    have h1 : t * (2 ^ 510 * od + 1075052609 * 2 ^ 480) ≤ t * Op :=
      mul_le_mul_of_nonpos_left (le_of_lt hOp_hi) htneg
    have h2 : (2:Int) ^ 510 * (2 ^ 128 * tod) ≤ 2 ^ 510 * (t * od) :=
      mul_le_mul_of_nonneg_left htod_lo (by positivity)
    nlinarith [h1, h2]

/-! ## Link 1 (over side): `r0` vs the grid rational, shared-`Ev` cancellation -/

/-- **Joint link-1 over (nonneg half, `r0 ≥ 2¹²⁶`)**: the shared even truncation cancels through
the floor, `r0·DENv − 2¹²⁶·NUMv ≤ Wev·2⁵⁹⁰·(r0 − 2¹²⁶)`. -/
theorem link1_over_tight {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) (hr0ge : (2:Int) ^ 126 ≤ int256 (r0Tree x)) :
    int256 (r0Tree x) * DENv (vTree x) (int256 (tTree x)) -
        2 ^ 126 * NUMv (vTree x) (int256 (tTree x)) ≤
      283678831804417 * 2 ^ 590 * (int256 (r0Tree x) - 2 ^ 126) := by
  obtain ⟨hfloor_lo, _⟩ := r0_floor_sandwich hx hC hC0
  obtain ⟨hEp_lo, hEp_hi, _, _⟩ := bridge_facts hx hC hC0
  obtain ⟨htOp_lo, _⟩ := tOd_bracket_nonneg hx hC hC0 htnn
  unfold NUMv DENv
  set r0 := int256 (r0Tree x) with hr0def
  set ev := (evTree x : Int) with hevdef
  set tod := int256 (todTree x) with htoddef
  set t := int256 (tTree x) with htdef
  set Ep := (evNumV (vTree x) : Int) with hEpdef
  set Op := (odNumV (vTree x) : Int) with hOpdef
  have hr0m : (0:Int) ≤ r0 - 2 ^ 126 := by linarith [hr0ge]
  have hr0p : (0:Int) ≤ r0 + 2 ^ 126 := by linarith [hr0ge]
  -- Ep·2^110·(r0−2^126) ≤ (2^638·ev + Wev·2^590)·(r0−2^126)
  have hterm1 : Ep * 2 ^ 110 * (r0 - 2 ^ 126) ≤
      (2 ^ 638 * ev + 283678831804417 * 2 ^ 590) * (r0 - 2 ^ 126) := by
    apply mul_le_mul_of_nonneg_right _ hr0m
    nlinarith [hEp_hi]
  -- −(t·Op)·(r0+2^126) ≤ −(2^638·tod)·(r0+2^126)
  have hterm2 : 2 ^ 638 * tod * (r0 + 2 ^ 126) ≤ t * Op * (r0 + 2 ^ 126) :=
    mul_le_mul_of_nonneg_right (by linarith [htOp_lo]) hr0p
  -- floor: r0·den − 2^126·num ≤ 0, scaled by 2^638
  have hfloor : r0 * (ev - tod) - 2 ^ 126 * (ev + tod) ≤ 0 := by linarith [hfloor_lo]
  have hfloor638 : (2:Int) ^ 638 * (r0 * (ev - tod) - 2 ^ 126 * (ev + tod)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hfloor
  nlinarith [hterm1, hterm2, hfloor638]

/-- **Link-1 over (nonneg half, `r0 ≤ 2¹²⁶`)**: the residue is nonpositive outright. -/
theorem link1_over_small {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) (hr0le : int256 (r0Tree x) ≤ (2:Int) ^ 126) :
    int256 (r0Tree x) * DENv (vTree x) (int256 (tTree x)) -
        2 ^ 126 * NUMv (vTree x) (int256 (tTree x)) ≤ 0 := by
  obtain ⟨hfloor_lo, _⟩ := r0_floor_sandwich hx hC hC0
  obtain ⟨hEp_lo, _, _, _⟩ := bridge_facts hx hC hC0
  obtain ⟨htOp_lo, _⟩ := tOd_bracket_nonneg hx hC hC0 htnn
  unfold NUMv DENv
  set r0 := int256 (r0Tree x) with hr0def
  set ev := (evTree x : Int) with hevdef
  set tod := int256 (todTree x) with htoddef
  set t := int256 (tTree x) with htdef
  set Ep := (evNumV (vTree x) : Int) with hEpdef
  set Op := (odNumV (vTree x) : Int) with hOpdef
  obtain ⟨hr0lo, _⟩ := r0Tree_bounds hx hC hC0
  have hr0nn : (0:Int) ≤ r0 := by
    have : (0:Int) < 2 ^ 123 := by positivity
    linarith [hr0lo]
  have hr0m : r0 - 2 ^ 126 ≤ 0 := by linarith [hr0le]
  have hr0p : (0:Int) ≤ r0 + 2 ^ 126 := by positivity
  -- Ep·2^110·(r0−2^126) ≤ 2^638·ev·(r0−2^126)  (Ep·2^110 ≥ 2^638·ev, factor ≤ 0)
  have hterm1 : Ep * 2 ^ 110 * (r0 - 2 ^ 126) ≤ 2 ^ 638 * ev * (r0 - 2 ^ 126) := by
    apply mul_le_mul_of_nonpos_right _ hr0m
    nlinarith [hEp_lo]
  have hterm2 : 2 ^ 638 * tod * (r0 + 2 ^ 126) ≤ t * Op * (r0 + 2 ^ 126) :=
    mul_le_mul_of_nonneg_right (by linarith [htOp_lo]) hr0p
  have hfloor : r0 * (ev - tod) - 2 ^ 126 * (ev + tod) ≤ 0 := by linarith [hfloor_lo]
  have hfloor638 : (2:Int) ^ 638 * (r0 * (ev - tod) - 2 ^ 126 * (ev + tod)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hfloor
  nlinarith [hterm1, hterm2, hfloor638]

/-- **Link-1 over (nonpositive half)**: the even truncation drops (`r0 ≤ 2¹²⁶`); the odd truncation
survives attenuated to the `t`-scale: `r0·DENv − 2¹²⁶·NUMv ≤ Wod·2⁴⁸⁰·(−t)·(r0 + 2¹²⁶)`. -/
theorem link1_over_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) :
    int256 (r0Tree x) * DENv (vTree x) (int256 (tTree x)) -
        2 ^ 126 * NUMv (vTree x) (int256 (tTree x)) ≤
      1075052609 * 2 ^ 480 * (-(int256 (tTree x))) * (int256 (r0Tree x) + 2 ^ 126) := by
  obtain ⟨hfloor_lo, _⟩ := r0_floor_sandwich hx hC hC0
  obtain ⟨hEp_lo, _, _, _⟩ := bridge_facts hx hC hC0
  obtain ⟨_, htOp_lo⟩ := tOd_bracket_neg hx hC hC0 htneg
  have hr0le := r0_le_2126_neg hx hC hC0 htneg
  unfold NUMv DENv
  set r0 := int256 (r0Tree x) with hr0def
  set ev := (evTree x : Int) with hevdef
  set tod := int256 (todTree x) with htoddef
  set t := int256 (tTree x) with htdef
  set Ep := (evNumV (vTree x) : Int) with hEpdef
  set Op := (odNumV (vTree x) : Int) with hOpdef
  obtain ⟨hr0lo, _⟩ := r0Tree_bounds hx hC hC0
  have hr0nn : (0:Int) ≤ r0 := by
    have : (0:Int) < 2 ^ 123 := by positivity
    linarith [hr0lo]
  have hr0m : r0 - 2 ^ 126 ≤ 0 := by linarith [hr0le]
  have hr0p : (0:Int) ≤ r0 + 2 ^ 126 := by positivity
  have hterm1 : Ep * 2 ^ 110 * (r0 - 2 ^ 126) ≤ 2 ^ 638 * ev * (r0 - 2 ^ 126) := by
    apply mul_le_mul_of_nonpos_right _ hr0m
    nlinarith [hEp_lo]
  -- −(t·Op)·(r0+2^126) ≤ (−2^638·tod + Wod·2^480·(−t))·(r0+2^126)
  have hterm2 : (2 ^ 638 * tod - 1075052609 * 2 ^ 480 * (-t)) * (r0 + 2 ^ 126) ≤
      t * Op * (r0 + 2 ^ 126) :=
    mul_le_mul_of_nonneg_right htOp_lo hr0p
  have hfloor : r0 * (ev - tod) - 2 ^ 126 * (ev + tod) ≤ 0 := by linarith [hfloor_lo]
  have hfloor638 : (2:Int) ^ 638 * (r0 * (ev - tod) - 2 ^ 126 * (ev + tod)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hfloor
  nlinarith [hterm1, hterm2, hfloor638]

/-! ## Denominator bounds for the grid rational in runtime terms -/

/-- On the nonneg half `DENv` brackets the runtime denominator:
`2⁶³⁸·(den − 2) ≤ DENv ≤ 2⁶³⁸·den + Wev·2⁵⁹⁰` (`den = ev − tod`). -/
theorem DENv_runtime_bracket {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    2 ^ 638 * ((evTree x : Int) - int256 (todTree x)) - 2 * 2 ^ 638 ≤
        DENv (vTree x) (int256 (tTree x)) ∧
      DENv (vTree x) (int256 (tTree x)) ≤
        2 ^ 638 * ((evTree x : Int) - int256 (todTree x)) + 283678831804417 * 2 ^ 590 := by
  obtain ⟨hEp_lo, hEp_hi, _, _⟩ := bridge_facts hx hC hC0
  obtain ⟨htOp_lo, htOp_hi⟩ := tOd_bracket_nonneg hx hC hC0 htnn
  obtain ⟨_, hthi⟩ := tTree_in_cert_domain hx hC hC0
  unfold DENv
  set ev := (evTree x : Int) with hevdef
  set tod := int256 (todTree x) with htoddef
  set t := int256 (tTree x) with htdef
  set Ep := (evNumV (vTree x) : Int) with hEpdef
  set Op := (odNumV (vTree x) : Int) with hOpdef
  constructor
  · -- lower: Ep·2^110 ≥ 2^638·ev; t·Op ≤ 2^638·tod + 2^638 + Wod·2^480·t, t ≤ H128;
    -- Wod·2^480·H128 + 2^638 ≤ 2·2^638
    have h1 : 2 ^ 638 * ev ≤ Ep * 2 ^ 110 := by nlinarith [hEp_lo]
    have h2 : 1075052609 * 2 ^ 480 * t ≤
        1075052609 * 2 ^ 480 * 117932881612756647068972071382077242199 :=
      mul_le_mul_of_nonneg_left hthi (by positivity)
    have h3 : (1075052609 * 2 ^ 480 * 117932881612756647068972071382077242199 : Int) + 2 ^ 638 ≤
        2 * 2 ^ 638 := by norm_num
    linarith [h1, htOp_hi, h2, h3]
  · -- upper: Ep·2^110 ≤ 2^638·ev + Wev·2^590; t·Op ≥ 2^638·tod
    have h1 : Ep * 2 ^ 110 ≤ 2 ^ 638 * ev + 283678831804417 * 2 ^ 590 := by nlinarith [hEp_hi]
    linarith [h1, htOp_lo]

/-- On the nonpositive half `DENv` dominates the scaled even accumulator: `2⁶³⁸·ev ≤ DENv`. -/
theorem DENv_ge_ev_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) :
    2 ^ 638 * (evTree x : Int) ≤ DENv (vTree x) (int256 (tTree x)) := by
  obtain ⟨hEp_lo, _, _, hOp_hi⟩ := bridge_facts hx hC hC0
  unfold DENv
  have hOp_nn : (0:Int) ≤ (odNumV (vTree x) : Int) := Int.natCast_nonneg _
  have htOp : int256 (tTree x) * (odNumV (vTree x) : Int) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg htneg hOp_nn
  nlinarith [hEp_lo, htOp]

/-- On the nonneg half `NUMv` dominates the scaled runtime numerator: `2⁶³⁸·num ≤ NUMv`. -/
theorem NUMv_ge_num {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    2 ^ 638 * ((evTree x : Int) + int256 (todTree x)) ≤ NUMv (vTree x) (int256 (tTree x)) := by
  obtain ⟨hEp_lo, _, _, _⟩ := bridge_facts hx hC hC0
  obtain ⟨htOp_lo, _⟩ := tOd_bracket_nonneg hx hC hC0 htnn
  unfold NUMv
  nlinarith [hEp_lo, htOp_lo]

/-! ## The cert `Real.exp` bounds at the runtime reduced argument

Instantiating the v-form Taylor caps (`ExpCertV.capExpUp`/`capExpLo`, `2⁻¹³¹` nudge) at
`t = int256 (tTree x)` and pushing through the abstract `Common.RealExpBridge` brackets
`Real.exp(t/2¹²⁸)` by the margin-nudged rational `ê = NE/DE`. -/

open ExpRealSpec Real Common.RealExpBridge Common.Exp

noncomputable section

/-- **Never-over cert real bound (nonneg half).** `(2¹³¹−1)·NE / (2¹³¹·DE) ≤ exp(t/2¹²⁸)`. -/
theorem certLo_real {t : Int} (h1 : 0 ≤ t) (h2 : t ≤ (ExpCertV.H128 : Int)) :
    ((2 ^ 131 - 1 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real) /
        (((2 ^ 131 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real)) ≤
      Real.exp ((t : Real) / (2 ^ 128 : Real)) := by
  have hcap := ExpCertV.capExpLo h1 h2
  have hwpos : 0 < (evalPoly ExpCertV.wLB t).toNat := by
    have hpos : 0 < evalPoly ExpCertV.wLB t := by
      rw [ExpCertV.evalWLB]
      exact mul_pos (by norm_num) (by have := certDE_pos h1 h2; omega)
    omega
  have h := le_exp_of_capLB (q := ExpCertV.Qexp) ExpCertV.Qexp_pos hwpos hcap
  have htn : (t.toNat : Int) = t := Int.toNat_of_nonneg h1
  have hylb : 0 ≤ evalPoly ExpCertV.yLB t := by
    rw [ExpCertV.evalYLB]; exact Int.mul_nonneg (by norm_num) (certNE_nonneg h1 h2)
  have hwlb : 0 ≤ evalPoly ExpCertV.wLB t := by
    rw [ExpCertV.evalWLB]
    exact Int.mul_nonneg (by norm_num) (by have := certDE_pos h1 h2; omega)
  have hyn : ((evalPoly ExpCertV.yLB t).toNat : Int) = evalPoly ExpCertV.yLB t := Int.toNat_of_nonneg hylb
  have hwn : ((evalPoly ExpCertV.wLB t).toNat : Int) = evalPoly ExpCertV.wLB t := Int.toNat_of_nonneg hwlb
  have harg : ((t.toNat : Nat) : Real) / ((ExpCertV.Qexp : Nat) : Real) = (t : Real) / (2 ^ 128 : Real) := by
    rw [show ((ExpCertV.Qexp : Nat) : Real) = (2 ^ 128 : Real) from by unfold ExpCertV.Qexp; norm_num]
    congr 1
    have : ((t.toNat : Nat) : Real) = (t : Real) := by
      have := htn; exact_mod_cast this
    exact this
  rw [harg] at h
  have hynr : ((evalPoly ExpCertV.yLB t).toNat : Real) = ((2 ^ 131 - 1 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real) := by
    have : ((evalPoly ExpCertV.yLB t).toNat : Int) = (2 ^ 131 - 1) * evalPoly ExpCertV.numExpV t := by
      rw [hyn, ExpCertV.evalYLB]
    have := congrArg (fun z : Int => (z : Real)) this
    push_cast at this ⊢; linarith [this]
  have hwnr : ((evalPoly ExpCertV.wLB t).toNat : Real) = ((2 ^ 131 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real) := by
    have : ((evalPoly ExpCertV.wLB t).toNat : Int) = 2 ^ 131 * evalPoly ExpCertV.denExpV t := by
      rw [hwn, ExpCertV.evalWLB]
    have := congrArg (fun z : Int => (z : Real)) this
    push_cast at this ⊢; linarith [this]
  rw [hynr, hwnr] at h
  exact h

/-- **Not-two-below cert real bound (nonneg half).** `exp(t/2¹²⁸) ≤ (2¹³¹+1)·NE / (2¹³¹·DE)`. -/
theorem certUp_real {t : Int} (h1 : 0 ≤ t) (h2 : t ≤ (ExpCertV.H128 : Int)) :
    Real.exp ((t : Real) / (2 ^ 128 : Real)) ≤
      ((2 ^ 131 + 1 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real) /
        (((2 ^ 131 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real)) := by
  have hcap := ExpCertV.capExpUp h1 h2
  have hwpos : 0 < (evalPoly ExpCertV.wUB t).toNat := by
    have hpos : 0 < evalPoly ExpCertV.wUB t := by
      rw [ExpCertV.evalWUB]
      exact mul_pos (by norm_num) (by have := certDE_pos h1 h2; omega)
    omega
  have h := exp_le_of_capUB (q := ExpCertV.Qexp) ExpCertV.Qexp_pos hwpos hcap
  have htn : (t.toNat : Int) = t := Int.toNat_of_nonneg h1
  have hyub : 0 ≤ evalPoly ExpCertV.yUB t := by
    rw [ExpCertV.evalYUB]; exact Int.mul_nonneg (by norm_num) (certNE_nonneg h1 h2)
  have hwub : 0 ≤ evalPoly ExpCertV.wUB t := by
    rw [ExpCertV.evalWUB]
    exact Int.mul_nonneg (by norm_num) (by have := certDE_pos h1 h2; omega)
  have hyn : ((evalPoly ExpCertV.yUB t).toNat : Int) = evalPoly ExpCertV.yUB t := Int.toNat_of_nonneg hyub
  have hwn : ((evalPoly ExpCertV.wUB t).toNat : Int) = evalPoly ExpCertV.wUB t := Int.toNat_of_nonneg hwub
  have harg : ((t.toNat : Nat) : Real) / ((ExpCertV.Qexp : Nat) : Real) = (t : Real) / (2 ^ 128 : Real) := by
    rw [show ((ExpCertV.Qexp : Nat) : Real) = (2 ^ 128 : Real) from by unfold ExpCertV.Qexp; norm_num]
    congr 1
    have : ((t.toNat : Nat) : Real) = (t : Real) := by
      have := htn; exact_mod_cast this
    exact this
  rw [harg] at h
  have hynr : ((evalPoly ExpCertV.yUB t).toNat : Real) = ((2 ^ 131 + 1 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real) := by
    have : ((evalPoly ExpCertV.yUB t).toNat : Int) = (2 ^ 131 + 1) * evalPoly ExpCertV.numExpV t := by
      rw [hyn, ExpCertV.evalYUB]
    have := congrArg (fun z : Int => (z : Real)) this
    push_cast at this ⊢; linarith [this]
  have hwnr : ((evalPoly ExpCertV.wUB t).toNat : Real) = ((2 ^ 131 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real) := by
    have : ((evalPoly ExpCertV.wUB t).toNat : Int) = 2 ^ 131 * evalPoly ExpCertV.denExpV t := by
      rw [hwn, ExpCertV.evalWUB]
    have := congrArg (fun z : Int => (z : Real)) this
    push_cast at this ⊢; linarith [this]
  rw [hynr, hwnr] at h
  exact h

/-- **Not-too-below cert real bound (negative half).** For `t ≤ 0` with `−t ∈ [0, H128]`:
`exp(t/2¹²⁸) ≤ (2¹³¹·NE) / ((2¹³¹−1)·DE)`. -/
theorem certUp_real_neg {t : Int} (h1 : t ≤ 0) (h2 : (-t) ≤ (ExpCertV.H128 : Int)) :
    Real.exp ((t : Real) / (2 ^ 128 : Real)) ≤
      ((2 ^ 131 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real) /
        (((2 ^ 131 - 1 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real)) := by
  have hnt : 0 ≤ -t := by omega
  have hcl := certLo_real hnt h2
  rw [numExpV_neg_eq_denExpV, denExpV_neg_eq_numExpV] at hcl
  obtain ⟨hNEpos, hDEpos⟩ := certNE_pos_neg_aux h1 h2
  have hNER : (0 : Real) < (evalPoly ExpCertV.numExpV t : Real) := by exact_mod_cast hNEpos
  have hDER : (0 : Real) < (evalPoly ExpCertV.denExpV t : Real) := by exact_mod_cast hDEpos
  have hexpneg : Real.exp (((-t) : Int) / (2 ^ 128 : Real)) =
      (Real.exp ((t : Real) / (2 ^ 128 : Real)))⁻¹ := by
    rw [show (((-t):Int) : Real) / (2 ^ 128 : Real) = -((t : Real) / (2 ^ 128 : Real)) from by
      push_cast; ring, Real.exp_neg]
  rw [hexpneg] at hcl
  have hexppos := Real.exp_pos ((t : Real) / (2 ^ 128 : Real))
  have hlhs_pos : (0:Real) < ((2 ^ 131 - 1 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real) /
      (((2 ^ 131 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real)) := by positivity
  rw [le_inv_comm₀ hlhs_pos hexppos] at hcl
  calc Real.exp ((t : Real) / (2 ^ 128 : Real))
      ≤ (((2 ^ 131 - 1 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real) /
          (((2 ^ 131 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real)))⁻¹ := hcl
    _ = ((2 ^ 131 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real) /
          (((2 ^ 131 - 1 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real)) := by
        rw [inv_div]

/-- **Never-over cert real bound (negative half).** For `t ≤ 0` with `−t ∈ [0, H128]`:
`(2¹³¹·NE) / ((2¹³¹+1)·DE) ≤ exp(t/2¹²⁸)`. -/
theorem certLo_real_neg {t : Int} (h1 : t ≤ 0) (h2 : (-t) ≤ (ExpCertV.H128 : Int)) :
    ((2 ^ 131 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real) /
        (((2 ^ 131 + 1 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real)) ≤
      Real.exp ((t : Real) / (2 ^ 128 : Real)) := by
  have hnt : 0 ≤ -t := by omega
  have hcu := certUp_real hnt h2
  rw [numExpV_neg_eq_denExpV, denExpV_neg_eq_numExpV] at hcu
  obtain ⟨hNEpos, hDEpos⟩ := certNE_pos_neg_aux h1 h2
  have hNER : (0 : Real) < (evalPoly ExpCertV.numExpV t : Real) := by exact_mod_cast hNEpos
  have hDER : (0 : Real) < (evalPoly ExpCertV.denExpV t : Real) := by exact_mod_cast hDEpos
  have hexpneg : Real.exp (((-t) : Int) / (2 ^ 128 : Real)) =
      (Real.exp ((t : Real) / (2 ^ 128 : Real)))⁻¹ := by
    rw [show (((-t):Int) : Real) / (2 ^ 128 : Real) = -((t : Real) / (2 ^ 128 : Real)) from by
      push_cast; ring, Real.exp_neg]
  rw [hexpneg] at hcu
  have hexppos := Real.exp_pos ((t : Real) / (2 ^ 128 : Real))
  have hrhs_pos : (0:Real) < ((2 ^ 131 + 1 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real) /
      (((2 ^ 131 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real)) := by positivity
  rw [inv_le_comm₀ hexppos hrhs_pos] at hcu
  calc ((2 ^ 131 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real) /
        (((2 ^ 131 + 1 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real))
      = (((2 ^ 131 + 1 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real) /
          (((2 ^ 131 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real)))⁻¹ := by
        rw [inv_div]
    _ ≤ Real.exp ((t : Real) / (2 ^ 128 : Real)) := hcu

/-- `t/2¹²⁸ ≤ 0` gives the cert domain `−t ≤ H128` for the negative half. -/
theorem tdom_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) : (-(int256 (tTree x))) ≤ (ExpCertV.H128 : Int) := by
  obtain ⟨htlo, _⟩ := tTree_in_cert_domain hx hC hC0
  rw [show ((ExpCertV.H128 : Nat) : Int) = 117932881612756647068972071382077242199 from by
    unfold ExpCertV.H128; norm_num]
  omega

/-! ## Analytic helpers on the reduced argument -/

/-- On the nonnegative half of the region the reduced argument is below `ln2/2`:
`t/2¹²⁸ ≤ log 2 / 2`. -/
theorem t_over_2128_le_half_log2 {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (int256 (tTree x) : Real) / (2 ^ 128 : Real) ≤ Real.log 2 / 2 := by
  obtain ⟨_, hthi⟩ := tTree_in_cert_domain hx hC hC0
  have hln2lo := ln2_lower
  rw [LN2c_eq] at hln2lo
  have htR : (int256 (tTree x) : Real) ≤ (117932881612756647068972071382077242199 : Real) := by
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hthi; push_cast at this; linarith [this]
  have hp128 : (0 : Real) < (2 ^ 128 : Real) := by positivity
  rw [div_le_div_iff₀ hp128 (by norm_num : (0:Real) < 2)]
  have hkey : (2 : Real) * (117932881612756647068972071382077242199 : Real) ≤ Real.log 2 * (2 ^ 128 : Real) := by
    have h1 : (38271408169742254668347313025622401492114385419650052359639581444463709 : Real) / (2 ^ 235 : Real) * (2 ^ 128 : Real) ≤ Real.log 2 * (2 ^ 128 : Real) := by
      apply mul_le_mul_of_nonneg_right hln2lo (by positivity)
    have h2 : (2 : Real) * (117932881612756647068972071382077242199 : Real) ≤
        (38271408169742254668347313025622401492114385419650052359639581444463709 : Real) / (2 ^ 235 : Real) * (2 ^ 128 : Real) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:Real) < 2 ^ 235)]
      norm_num
    linarith [h1, h2]
  nlinarith [htR, hkey]

/-- `exp(t/2¹²⁸) ≤ √2` on the nonneg half. -/
theorem exp_t_le_sqrt2 {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    Real.exp ((int256 (tTree x) : Real) / (2 ^ 128 : Real)) ≤ Real.sqrt 2 := by
  have hle := t_over_2128_le_half_log2 hx hC hC0
  calc Real.exp ((int256 (tTree x) : Real) / (2 ^ 128 : Real))
      ≤ Real.exp (Real.log 2 / 2) := Real.exp_le_exp.mpr hle
    _ = Real.sqrt 2 := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0:Real) < 2)]; ring_nf

/-- The convexity bound `exp(b) − exp(a) ≤ (b−a)·exp(b)`. -/
theorem exp_diff_le (a b : Real) : Real.exp b - Real.exp a ≤ (b - a) * Real.exp b := by
  have key : Real.exp a = Real.exp (a - b) * Real.exp b := by rw [← Real.exp_add]; ring_nf
  have h1 : a - b + 1 ≤ Real.exp (a - b) := Real.add_one_le_exp (a - b)
  have hb : 0 < Real.exp b := Real.exp_pos b
  rw [key]; nlinarith [h1, hb]

/-- The reduced argument is above `−log 2` on the region, so `exp(rt) > 1/2`. -/
theorem exp_reducedArg_gt_half {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (1 : Real) / 2 < Real.exp (reducedArg x) := by
  obtain ⟨htlo, _⟩ := tTree_in_cert_domain hx hC hC0
  have hclose := abs_lt.mp (reducedArg_close hx hC hC0)
  have hp128 : (0 : Real) < (2 ^ 128 : Real) := by positivity
  have htR : -(117932881612756647068972071382077242199 : Real) ≤ (int256 (tTree x) : Real) := by
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr htlo; push_cast at this; linarith [this]
  have hln2 : (0.6931471805 : Real) ≤ Real.log 2 := by
    have := ln2_lower; rw [LN2c_eq] at this
    have h2 : (0.6931471805 : Real) ≤
        (38271408169742254668347313025622401492114385419650052359639581444463709 : Real) / (2 ^ 235 : Real) := by
      rw [le_div_iff₀ (by positivity : (0:Real) < 2 ^ 235)]; norm_num
    linarith [this, h2]
  have htdiv : -(0.35 : Real) ≤ (int256 (tTree x) : Real) / (2 ^ 128 : Real) := by
    rw [le_div_iff₀ hp128]; nlinarith [htR]
  have h9 : (9 : Real) / (8 * (2 ^ 128 : Real)) ≤ 0.34 := by
    rw [div_le_iff₀ (by positivity)]; norm_num
  have hrt : -(Real.log 2) < reducedArg x := by linarith [hclose.1, htdiv, h9, hln2]
  have : Real.exp (-(Real.log 2)) < Real.exp (reducedArg x) := Real.exp_lt_exp.mpr hrt
  rwa [Real.exp_neg, Real.exp_log (by norm_num : (0:Real) < 2), show (2:Real)⁻¹ = 1/2 from by norm_num] at this

/-! ## The `r0 ≤ 1.4146·2¹²⁶` cap and the runtime numerator ceiling

The grid rational is capped through links 2–3: `ê(v) ≤ ê(t²) + grain ≤ √2·Mp + grain ≤ 14145/10⁴`.
Pulling that back through the truncation brackets caps the runtime numerator
(`10⁴·num ≤ 14145·den + 28290`, hence `100·num ≤ 145·den`) and the quotient
(`10⁴·(r0 − 2¹²⁶) ≤ 4146·2¹²⁶`). -/

/-- The grid rational is below `14145/10000` on the nonneg half. -/
theorem Qv_le_14145 {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    (NUMv (vTree x) (int256 (tTree x)) : Real) / (DENv (vTree x) (int256 (tTree x)) : Real) ≤
      14145 / 10000 := by
  obtain ⟨_, hgran⟩ := gran_over_pair hx hC hC0 htnn
  obtain ⟨_, hthi⟩ := tTree_in_cert_domain hx hC hC0
  set t := int256 (tTree x) with htdef
  have htdom : t ≤ (ExpCertV.H128 : Int) := by
    rw [show ((ExpCertV.H128 : Nat) : Int) = 117932881612756647068972071382077242199 from by
      unfold ExpCertV.H128; norm_num]
    exact hthi
  have hDE : (1:Int) ≤ evalPoly ExpCertV.denExpV t := certDE_pos htnn htdom
  have hDER : (0:Real) < (evalPoly ExpCertV.denExpV t : Real) := by
    have : (0:Int) < evalPoly ExpCertV.denExpV t := lt_of_lt_of_le one_pos hDE
    exact_mod_cast this
  have hNEnn : (0:Real) ≤ (evalPoly ExpCertV.numExpV t : Real) := by
    have := certNE_nonneg htnn htdom; exact_mod_cast this
  -- NE/DE ≤ Et·Mp ≤ √2·(2^131/(2^131−1)) ≤ 14144/10000
  have hcertlo := certLo_real htnn htdom
  set Et := Real.exp ((t : Real) / (2 ^ 128 : Real)) with hEtdef
  have hEtsqrt2 := exp_t_le_sqrt2 hx hC hC0
  rw [← hEtdef] at hEtsqrt2
  have hNEDE_le : (evalPoly ExpCertV.numExpV t : Real) / (evalPoly ExpCertV.denExpV t : Real) ≤
      Et * ((2 ^ 131 : Real) / ((2 ^ 131 : Real) - 1)) := by
    have hc : ((2 ^ 131 - 1 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real) /
        (((2 ^ 131 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real)) ≤ Et := hcertlo
    have key : (evalPoly ExpCertV.numExpV t : Real) / (evalPoly ExpCertV.denExpV t : Real) =
        ((2 ^ 131 : Real) / ((2 ^ 131 : Real) - 1)) *
          (((2 ^ 131 - 1 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real) /
            (((2 ^ 131 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real))) := by
      push_cast; field_simp; ring
    rw [key, mul_comm Et _]
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  have hsqrt2_val : Real.sqrt 2 ≤ 14143 / 10000 := by
    rw [Real.sqrt_le_iff]; constructor <;> norm_num
  have hMp_le : ((2 ^ 131 : Real) / ((2 ^ 131 : Real) - 1)) ≤ 14144 / 14143 := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    have h131 : (14144 : Real) ≤ 2 ^ 131 := by norm_num
    nlinarith [h131]
  have hNEDE14144 : (evalPoly ExpCertV.numExpV t : Real) / (evalPoly ExpCertV.denExpV t : Real) ≤
      14144 / 10000 := by
    have hEtnn : (0:Real) ≤ Et := le_of_lt (Real.exp_pos _)
    have h1 : Et * ((2 ^ 131 : Real) / ((2 ^ 131 : Real) - 1)) ≤
        (14143 / 10000) * (14144 / 14143) := by
      apply mul_le_mul (le_trans hEtsqrt2 hsqrt2_val) hMp_le (by positivity) (by norm_num)
    have h2 : (14143 / 10000 : Real) * (14144 / 14143) = 14144 / 10000 := by norm_num
    linarith [hNEDE_le, h1, h2 ▸ h1]
  -- add the grain: 2^126·Qv ≤ 2^126·(NE/DE) + 0.33 ⟹ Qv ≤ 14144/10000 + 0.33/2^126 ≤ 14145/10000
  have h2126 : (2 ^ 126 : Real) * ((NUMv (vTree x) t : Real) / (DENv (vTree x) t : Real)) ≤
      (2 ^ 126 : Real) * (14144 / 10000) + 3290521163436398582 / 10000000000000000000 := by
    have := mul_le_mul_of_nonneg_left hNEDE14144 (by positivity : (0:Real) ≤ (2:Real) ^ 126)
    linarith [hgran, this]
  have hfin : (2 ^ 126 : Real) * (14144 / 10000) + 3290521163436398582 / 10000000000000000000 ≤
      (2 ^ 126 : Real) * (14145 / 10000) := by norm_num
  have hp : (0:Real) < (2 ^ 126 : Real) := by positivity
  exact le_of_mul_le_mul_left (le_trans h2126 hfin) hp

/-- The runtime numerator ceiling: `10⁴·num ≤ 14145·den + 28290`. -/
theorem num_ceiling {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    10000 * ((evTree x : Int) + int256 (todTree x)) ≤
      14145 * ((evTree x : Int) - int256 (todTree x)) + 28290 := by
  have hQv := Qv_le_14145 hx hC hC0 htnn
  obtain ⟨hthi_lo, hthi⟩ := tTree_in_cert_domain hx hC hC0
  have hvle := vTree_le_vmax hx hC hC0
  set t := int256 (tTree x) with htdef
  set v := vTree x with hvdef
  have hD : 554482771859 * 2 ^ 725 ≤ DENv v t := DENv_ge_over (by omega) hthi
  have hDpos : (0:Int) < DENv v t := lt_of_lt_of_le (by positivity) hD
  have hDR : (0:Real) < (DENv v t : Real) := by exact_mod_cast hDpos
  -- 10000·NUMv ≤ 14145·DENv (from the real cap)
  have hNUM_le : 10000 * NUMv v t ≤ 14145 * DENv v t := by
    have hR : (NUMv v t : Real) ≤ (14145 / 10000) * (DENv v t : Real) := by
      have := mul_le_mul_of_nonneg_right hQv (le_of_lt hDR)
      rwa [div_mul_cancel₀ _ (ne_of_gt hDR)] at this
    have hR2 : (10000 : Real) * (NUMv v t : Real) ≤ 14145 * (DENv v t : Real) := by
      nlinarith [hR]
    exact_mod_cast hR2
  -- pull back through the brackets: 2^638·num ≤ NUMv; DENv ≤ 2^638·den + Wev·2^590
  have hNUM_ge := NUMv_ge_num hx hC hC0 htnn
  obtain ⟨_, hDEN_le⟩ := DENv_runtime_bracket hx hC hC0 htnn
  set num := (evTree x : Int) + int256 (todTree x) with hnumdef
  set den := (evTree x : Int) - int256 (todTree x) with hdendef
  -- 10000·2^638·num ≤ 14145·(2^638·den + Wev·2^590) ≤ 2^638·(14145·den + 28290)
  have hchain : 10000 * (2 ^ 638 * num) ≤ 2 ^ 638 * (14145 * den + 28290) := by
    have h1 : 10000 * (2 ^ 638 * num) ≤ 10000 * NUMv v t :=
      mul_le_mul_of_nonneg_left hNUM_ge (by norm_num)
    have h2 : 14145 * DENv v t ≤ 14145 * (2 ^ 638 * den + 283678831804417 * 2 ^ 590) :=
      mul_le_mul_of_nonneg_left hDEN_le (by norm_num)
    have h3 : (14145 : Int) * (2 ^ 638 * den + 283678831804417 * 2 ^ 590) ≤
        2 ^ 638 * (14145 * den + 28290) := by
      have hW : (14145 : Int) * (283678831804417 * 2 ^ 590) ≤ 28290 * 2 ^ 638 := by norm_num
      nlinarith [hW]
    linarith [h1, hNUM_le, h2, h3]
  have hp : (0:Int) < 2 ^ 638 := by positivity
  have h2 : 2 ^ 638 * (10000 * num) ≤ 2 ^ 638 * (14145 * den + 28290) := by linarith [hchain]
  exact le_of_mul_le_mul_left h2 hp

/-- `100·num ≤ 145·den` (`ê ≤ 1.45`) on the nonneg half. -/
theorem num_le_145_den {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    100 * ((evTree x : Int) + int256 (todTree x)) ≤ 145 * ((evTree x : Int) - int256 (todTree x)) := by
  have hceil := num_ceiling hx hC hC0 htnn
  have hden := den_ge_072 hx hC hC0
  set num := (evTree x : Int) + int256 (todTree x) with hnumdef
  set den := (evTree x : Int) - int256 (todTree x) with hdendef
  -- 100·(10000·num) ≤ 100·(14145·den + 28290) ≤ 10000·(145·den) since 355·den ≥ 2829000
  nlinarith [hceil, hden]

/-- The quotient cap: `10⁴·(r0 − 2¹²⁶) ≤ 4146·2¹²⁶` on the nonneg half. -/
theorem r0_cap {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    10000 * (int256 (r0Tree x) - 2 ^ 126) ≤ 4146 * 2 ^ 126 := by
  obtain ⟨hfloor_lo, _⟩ := r0_floor_sandwich hx hC hC0
  have hceil := num_ceiling hx hC hC0 htnn
  have hden := den_ge_072 hx hC hC0
  set r0 := int256 (r0Tree x) with hr0def
  set num := (evTree x : Int) + int256 (todTree x) with hnumdef
  set den := (evTree x : Int) - int256 (todTree x) with hdendef
  have hdenpos : (0:Int) < den := lt_of_lt_of_le (by norm_num) hden
  -- 10000·(r0−2^126)·den ≤ 2^126·(10000·num − 10000·den) ≤ 2^126·(4145·den + 28290) ≤ 4146·2^126·den
  have h1 : 10000 * (r0 - 2 ^ 126) * den ≤ 2 ^ 126 * (4145 * den + 28290) := by
    nlinarith [hfloor_lo, hceil]
  have h2 : (2:Int) ^ 126 * (4145 * den + 28290) ≤ 4146 * 2 ^ 126 * den := by
    nlinarith [hden]
  have hchain : 10000 * (r0 - 2 ^ 126) * den ≤ 4146 * 2 ^ 126 * den := le_trans h1 h2
  exact le_of_mul_le_mul_right hchain hdenpos

/-! ## The per-point never-over (nonnegative half) -/

/-- The link-1 jitter divided by `DENv` stays inside its budget (nonneg half):
`Wev·2⁵⁹⁰·(r0 − 2¹²⁶)/DENv ≤ 6207065162659510332/10¹⁹`. -/
theorem jitter_over_budget {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    (283678831804417 : Real) * 2 ^ 590 * ((int256 (r0Tree x) : Real) - 2 ^ 126) /
        (DENv (vTree x) (int256 (tTree x)) : Real) ≤
      6207065162659510332 / 10000000000000000000 := by
  obtain ⟨_, hthi⟩ := tTree_in_cert_domain hx hC hC0
  have hvle := vTree_le_vmax hx hC hC0
  set r0 := int256 (r0Tree x) with hr0def
  set t := int256 (tTree x) with htdef
  set v := vTree x with hvdef
  have hD : 554482771859 * 2 ^ 725 ≤ DENv v t := DENv_ge_over (by omega) hthi
  have hDpos : (0:Int) < DENv v t := lt_of_lt_of_le (by positivity) hD
  have hDR : (0:Real) < (DENv v t : Real) := by exact_mod_cast hDpos
  rcases le_or_gt ((r0:Real) - 2^126) 0 with hle0 | hgt0
  · have hnumneg : (283678831804417 : Real) * 2 ^ 590 * ((r0 : Real) - 2 ^ 126) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hle0
    have : (283678831804417 : Real) * 2 ^ 590 * ((r0 : Real) - 2 ^ 126) / (DENv v t : Real) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hnumneg (le_of_lt hDR)
    linarith [this]
  · rw [div_le_iff₀ hDR]
    -- r0 − 2^126 ≤ 4146·2^126/10^4 (r0_cap); DENv ≥ 2^638·(den−2) ≥ 2^638·(den_lo−2)
    have hcap := r0_cap hx hC hC0 htnn
    have hcapR : (r0 : Real) - 2 ^ 126 ≤ 4146 * 2 ^ 126 / 10000 := by
      have h := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hcap
      push_cast at h
      linarith [h]
    obtain ⟨hDEN_ge, _⟩ := DENv_runtime_bracket hx hC hC0 htnn
    have hden := den_ge_072 hx hC hC0
    have hDENlow : (2:Int) ^ 638 * (61251667532612381706986956632087880162 - 2) ≤ DENv v t := by
      have : (2:Int) ^ 638 * (61251667532612381706986956632087880162 - 2) ≤
          2 ^ 638 * ((evTree x : Int) - int256 (todTree x)) - 2 * 2 ^ 638 := by
        nlinarith [hden]
      linarith [this, hDEN_ge]
    have hDENlowR : ((2:Real) ^ 638 * (61251667532612381706986956632087880162 - 2)) ≤
        (DENv v t : Real) := by
      have h := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hDENlow
      push_cast at h
      linarith [h]
    have hnum_le : (283678831804417 : Real) * 2 ^ 590 * ((r0 : Real) - 2 ^ 126) ≤
        (283678831804417 : Real) * 2 ^ 590 * (4146 * 2 ^ 126 / 10000) :=
      mul_le_mul_of_nonneg_left hcapR (by positivity)
    have hbudget : (283678831804417 : Real) * 2 ^ 590 * (4146 * 2 ^ 126 / 10000) ≤
        (6207065162659510332 / 10000000000000000000) *
          ((2:Real) ^ 638 * (61251667532612381706986956632087880162 - 2)) := by
      norm_num
    calc (283678831804417 : Real) * 2 ^ 590 * ((r0 : Real) - 2 ^ 126)
        ≤ (283678831804417 : Real) * 2 ^ 590 * (4146 * 2 ^ 126 / 10000) := hnum_le
      _ ≤ (6207065162659510332 / 10000000000000000000) *
          ((2:Real) ^ 638 * (61251667532612381706986956632087880162 - 2)) := hbudget
      _ ≤ (6207065162659510332 / 10000000000000000000) * (DENv v t : Real) :=
          mul_le_mul_of_nonneg_left hDENlowR (by norm_num)

/-- **The per-point never-over (nonneg half).** `r0 ≤ 2¹²⁶·exp(rt) + B` with the four-link budget
`B = 10050013498897899168/10¹⁹`: link-1 jitter `≤ 0.6207…`, granularity `≤ 0.3291…`, the `Mp`
factor `≤ √2·2¹²⁶/(2¹³¹−1) ≤ 0.0442…`, and the reduced-argument gap `≤ √2/128 ≤ 0.0111…`. -/
theorem r0_real_over_tight {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    (int256 (r0Tree x) : Real) ≤ (2 ^ 126 : Real) * Real.exp (reducedArg x) +
      10050013498897899168 / 10000000000000000000 := by
  obtain ⟨_, hthi⟩ := tTree_in_cert_domain hx hC hC0
  have hvle := vTree_le_vmax hx hC hC0
  set t := int256 (tTree x) with htdef
  set v := vTree x with hvdef
  have htdom : t ≤ (ExpCertV.H128 : Int) := by
    rw [show ((ExpCertV.H128 : Nat) : Int) = 117932881612756647068972071382077242199 from by
      unfold ExpCertV.H128; norm_num]
    exact hthi
  set r0 := int256 (r0Tree x) with hr0def
  have hD : 554482771859 * 2 ^ 725 ≤ DENv v t := DENv_ge_over (by omega) hthi
  have hDpos : (0:Int) < DENv v t := lt_of_lt_of_le (by positivity) hD
  have hDR : (0:Real) < (DENv v t : Real) := by exact_mod_cast hDpos
  have hDE : (1:Int) ≤ evalPoly ExpCertV.denExpV t := certDE_pos htnn htdom
  have hDER : (0:Real) < (evalPoly ExpCertV.denExpV t : Real) := by
    have : (0:Int) < evalPoly ExpCertV.denExpV t := lt_of_lt_of_le one_pos hDE
    exact_mod_cast this
  -- link 1: r0 ≤ 2^126·Qv + jitter
  have hlink1 : (r0 : Real) ≤ (2 ^ 126 : Real) * ((NUMv v t : Real) / (DENv v t : Real)) +
      6207065162659510332 / 10000000000000000000 := by
    rcases le_or_gt r0 (2^126) with hsm | hbg
    · have hi := link1_over_small hx hC hC0 htnn hsm
      have hiR : (r0 : Real) * (DENv v t : Real) ≤ (2 ^ 126 : Real) * (NUMv v t : Real) := by
        have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hi; push_cast at this; linarith [this]
      have hr0le : (r0 : Real) ≤ (2 ^ 126 : Real) * ((NUMv v t : Real) / (DENv v t : Real)) := by
        rw [mul_div_assoc', le_div_iff₀ hDR]; linarith [hiR]
      linarith [hr0le]
    · have hi := link1_over_tight hx hC hC0 htnn (le_of_lt hbg)
      have hjointR : (r0 : Real) * (DENv v t : Real) - (2 ^ 126 : Real) * (NUMv v t : Real) ≤
          (283678831804417 : Real) * 2 ^ 590 * ((r0 : Real) - 2 ^ 126) := by
        have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hi; push_cast at this; linarith [this]
      have hstep : (r0 : Real) ≤ (2 ^ 126 : Real) * (NUMv v t : Real) / (DENv v t : Real) +
          (283678831804417 : Real) * 2 ^ 590 * ((r0 : Real) - 2 ^ 126) / (DENv v t : Real) := by
        rw [div_add_div_same, le_div_iff₀ hDR]; nlinarith [hjointR, hDR]
      rw [mul_div_assoc] at hstep
      linarith [hstep, jitter_over_budget hx hC hC0 htnn]
  -- link 2: 2^126·Qv ≤ 2^126·(NE/DE) + grain
  obtain ⟨_, hgran⟩ := gran_over_pair hx hC hC0 htnn
  -- link 3: NE/DE ≤ Et·Mp; Mp excess ≤ √2·2^126/(2^131−1)
  have hcertlo := certLo_real htnn htdom
  set Et := Real.exp ((t : Real) / (2 ^ 128 : Real)) with hEtdef
  set NE := evalPoly ExpCertV.numExpV t with hNEdef
  set DE := evalPoly ExpCertV.denExpV t with hDEdef
  set Mp : Real := (2 ^ 131 : Real) / ((2 ^ 131 : Real) - 1) with hMpdef
  have hEtsqrt2 := exp_t_le_sqrt2 hx hC hC0
  rw [← hEtdef] at hEtsqrt2
  have hEtnn : (0 : Real) ≤ Et := le_of_lt (Real.exp_pos _)
  have hNEDE_le : (NE : Real) / (DE : Real) ≤ Et * Mp := by
    have hc : ((2 ^ 131 - 1 : Int) : Real) * (NE : Real) /
        (((2 ^ 131 : Int) : Real) * (DE : Real)) ≤ Et := hcertlo
    rw [hMpdef]
    have key : (NE : Real) / (DE : Real) =
        ((2 ^ 131 : Real) / ((2 ^ 131 : Real) - 1)) *
          (((2 ^ 131 - 1 : Int) : Real) * (NE : Real) /
            (((2 ^ 131 : Int) : Real) * (DE : Real))) := by
      push_cast; field_simp; ring
    rw [key, mul_comm Et _]; exact mul_le_mul_of_nonneg_left hc (by positivity)
  have hsqrt2_hi : Real.sqrt 2 ≤ 141421356237309504880168872421 / 100000000000000000000000000000 := by
    rw [Real.sqrt_le_iff]; constructor <;> norm_num
  have hsqrt2_nn : (0:Real) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hMp1 : Mp - 1 = 1 / ((2 ^ 131 : Real) - 1) := by rw [hMpdef]; field_simp
  have hcMp : (2 ^ 126 : Real) * Et * (Mp - 1) ≤ 441941738241592203 / 10000000000000000000 := by
    rw [hMp1]
    have hb : (2 ^ 126 : Real) * Et * (1 / ((2 ^ 131 : Real) - 1)) ≤
        (2 ^ 126 : Real) * Real.sqrt 2 * (1 / ((2 ^ 131 : Real) - 1)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hEtsqrt2 (by positivity)
    have hn : (2 ^ 126 : Real) * Real.sqrt 2 * (1 / ((2 ^ 131 : Real) - 1)) ≤
        441941738241592203 / 10000000000000000000 := by
      rw [mul_one_div, div_le_div_iff₀ (by norm_num) (by norm_num)]
      nlinarith [hsqrt2_hi, hsqrt2_nn]
    linarith [hb, hn]
  -- link 4: 2^126·(Et − Ert) ≤ √2/128
  set Ert := Real.exp (reducedArg x) with hErtdef
  have hgapover := reducedArg_close_over hx hC hC0
  have hExp_diff : Et - Ert ≤ ((t : Real) / (2 ^ 128 : Real) - reducedArg x) * Et := exp_diff_le _ _
  have hcGap1 : (2 ^ 126 : Real) * (Et - Ert) ≤ 110485434560398051 / 10000000000000000000 := by
    have h1 : Et - Ert ≤ (1 / (32 * (2 ^ 128 : Real))) * Et :=
      le_trans hExp_diff (mul_le_mul_of_nonneg_right (le_of_lt hgapover) hEtnn)
    have h2 : (2 ^ 126 : Real) * (Et - Ert) ≤ (2 ^ 126 : Real) * ((1 / (32 * (2 ^ 128 : Real))) * Et) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (2 ^ 126 : Real) * ((1 / (32 * (2 ^ 128 : Real))) * Et) ≤
        (2 ^ 126 : Real) * ((1 / (32 * (2 ^ 128 : Real))) * Real.sqrt 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEtsqrt2 (by positivity)) (by positivity)
    have h4 : (2 ^ 126 : Real) * ((1 / (32 * (2 ^ 128 : Real))) * Real.sqrt 2) ≤
        110485434560398051 / 10000000000000000000 := by
      rw [show (2 ^ 126 : Real) * ((1 / (32 * (2 ^ 128 : Real))) * Real.sqrt 2) =
            Real.sqrt 2 * (2 ^ 126 / (32 * 2 ^ 128)) from by ring]
      have : (2 ^ 126 : Real) / (32 * 2 ^ 128) = 1 / 128 := by norm_num
      rw [this]; nlinarith [hsqrt2_hi, hsqrt2_nn]
    linarith [h2, h3, h4]
  -- assemble
  have hNEMp : (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) ≤
      (2 ^ 126 : Real) * Et + (2 ^ 126 : Real) * Et * (Mp - 1) := by
    have h := mul_le_mul_of_nonneg_left hNEDE_le (by positivity : (0:Real) ≤ (2 ^ 126 : Real))
    nlinarith [h]
  have hEtErt : (2 ^ 126 : Real) * Et ≤ (2 ^ 126 : Real) * Ert +
      110485434560398051 / 10000000000000000000 := by
    nlinarith [hcGap1]
  calc (r0 : Real) ≤ (2 ^ 126 : Real) * ((NUMv v t : Real) / (DENv v t : Real)) +
        6207065162659510332 / 10000000000000000000 := hlink1
    _ ≤ ((2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) +
          3290521163436398582 / 10000000000000000000) +
        6207065162659510332 / 10000000000000000000 := by linarith [hgran]
    _ ≤ (((2 ^ 126 : Real) * Et + 441941738241592203 / 10000000000000000000) +
          3290521163436398582 / 10000000000000000000) +
        6207065162659510332 / 10000000000000000000 := by linarith [hNEMp, hcMp]
    _ ≤ ((((2 ^ 126 : Real) * Ert + 110485434560398051 / 10000000000000000000) +
          441941738241592203 / 10000000000000000000) +
          3290521163436398582 / 10000000000000000000) +
        6207065162659510332 / 10000000000000000000 := by linarith [hEtErt]
    _ = (2 ^ 126 : Real) * Real.exp (reducedArg x) +
        10050013498897899168 / 10000000000000000000 := by rw [hErtdef]; ring

/-! ## The per-point never-over (nonpositive half) -/

/-- The link-1 jitter budget on the nonpositive half:
`Wod·2⁴⁸⁰·(−t)·(r0 + 2¹²⁶)/DENv ≤ 6207065162659510332/10¹⁹`. -/
theorem jitter_over_budget_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) :
    (1075052609 : Real) * 2 ^ 480 * (-(int256 (tTree x) : Real)) *
        ((int256 (r0Tree x) : Real) + 2 ^ 126) / (DENv (vTree x) (int256 (tTree x)) : Real) ≤
      6207065162659510332 / 10000000000000000000 := by
  obtain ⟨htlo, _⟩ := tTree_in_cert_domain hx hC hC0
  have hr0le := r0_le_2126_neg hx hC hC0 htneg
  obtain ⟨hr0lo, _⟩ := r0Tree_bounds hx hC hC0
  have hDEN_ge := DENv_ge_ev_neg hx hC hC0 htneg
  obtain ⟨hev_lo, _⟩ := evTree_facts (vTree_eq hx hC hC0).2
  set r0 := int256 (r0Tree x) with hr0def
  set t := int256 (tTree x) with htdef
  set v := vTree x with hvdef
  have hev : (103786963397729689639908782561058906594 : Int) ≤ (evTree x : Int) := by
    have : (0x4e14a45e5650b506e97f4c5da23861e2 : Int) ≤ (evTree x : Int) := by exact_mod_cast hev_lo
    rw [show (0x4e14a45e5650b506e97f4c5da23861e2 : Int) = 103786963397729689639908782561058906594 from by norm_num] at this
    exact this
  have hDEN_low : (2:Int) ^ 638 * 103786963397729689639908782561058906594 ≤ DENv v t := by
    have : (2:Int) ^ 638 * 103786963397729689639908782561058906594 ≤ 2 ^ 638 * (evTree x : Int) :=
      mul_le_mul_of_nonneg_left hev (by positivity)
    linarith [this, hDEN_ge]
  have hDpos : (0:Int) < DENv v t := lt_of_lt_of_le (by positivity) hDEN_low
  have hDR : (0:Real) < (DENv v t : Real) := by exact_mod_cast hDpos
  rw [div_le_iff₀ hDR]
  -- numerator ≤ Wod·2^480·H128·2·2^126; DENv ≥ 2^638·A0
  have hntR : (0:Real) ≤ -(t : Real) := by
    have : (t : Real) ≤ 0 := by exact_mod_cast htneg
    linarith
  have hntH : -(t : Real) ≤ 117932881612756647068972071382077242199 := by
    have h := (@Int.cast_le Real _ _ _ _ _ _ _).mpr htlo
    push_cast at h
    linarith [h]
  have hr0pR : (0:Real) ≤ (r0 : Real) + 2 ^ 126 := by
    have h : (0:Int) ≤ r0 := by
      have : (0:Int) < 2 ^ 123 := by positivity
      linarith [hr0lo]
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr h
    push_cast at this
    linarith [this]
  have hr0pH : (r0 : Real) + 2 ^ 126 ≤ 2 * 2 ^ 126 := by
    have h := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hr0le
    push_cast at h
    linarith [h]
  have hnum_le : (1075052609 : Real) * 2 ^ 480 * (-(t : Real)) * ((r0 : Real) + 2 ^ 126) ≤
      (1075052609 : Real) * 2 ^ 480 * 117932881612756647068972071382077242199 * (2 * 2 ^ 126) := by
    have h1 : (1075052609 : Real) * 2 ^ 480 * (-(t : Real)) ≤
        (1075052609 : Real) * 2 ^ 480 * 117932881612756647068972071382077242199 :=
      mul_le_mul_of_nonneg_left hntH (by positivity)
    exact mul_le_mul h1 hr0pH hr0pR (by positivity)
  have hDENlowR : ((2:Real) ^ 638 * 103786963397729689639908782561058906594) ≤ (DENv v t : Real) := by
    have h := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hDEN_low
    push_cast at h
    linarith [h]
  have hbudget : (1075052609 : Real) * 2 ^ 480 * 117932881612756647068972071382077242199 *
      (2 * 2 ^ 126) ≤ (6207065162659510332 / 10000000000000000000) *
        ((2:Real) ^ 638 * 103786963397729689639908782561058906594) := by
    norm_num
  calc (1075052609 : Real) * 2 ^ 480 * (-(t : Real)) * ((r0 : Real) + 2 ^ 126)
      ≤ (1075052609 : Real) * 2 ^ 480 * 117932881612756647068972071382077242199 * (2 * 2 ^ 126) :=
        hnum_le
    _ ≤ (6207065162659510332 / 10000000000000000000) *
        ((2:Real) ^ 638 * 103786963397729689639908782561058906594) := hbudget
    _ ≤ (6207065162659510332 / 10000000000000000000) * (DENv v t : Real) :=
        mul_le_mul_of_nonneg_left hDENlowR (by norm_num)

/-- **The per-point never-over (nonpositive half).** The granularity is free here; the `Mp` factor
and reduced-argument gap shrink (`Et ≤ 1`), so the same budget `B` covers the half. -/
theorem r0_real_over_tight_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) :
    (int256 (r0Tree x) : Real) ≤ (2 ^ 126 : Real) * Real.exp (reducedArg x) +
      10050013498897899168 / 10000000000000000000 := by
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
  -- link 1: r0 ≤ 2^126·Qv + jitter
  have hlink1 : (r0 : Real) ≤ (2 ^ 126 : Real) * ((NUMv v t : Real) / (DENv v t : Real)) +
      6207065162659510332 / 10000000000000000000 := by
    have hi := link1_over_neg hx hC hC0 htneg
    have hiR : (r0 : Real) * (DENv v t : Real) - (2 ^ 126 : Real) * (NUMv v t : Real) ≤
        (1075052609 : Real) * 2 ^ 480 * (-(t : Real)) * ((r0 : Real) + 2 ^ 126) := by
      have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hi; push_cast at this; linarith [this]
    have hstep : (r0 : Real) ≤ (2 ^ 126 : Real) * (NUMv v t : Real) / (DENv v t : Real) +
        (1075052609 : Real) * 2 ^ 480 * (-(t : Real)) * ((r0 : Real) + 2 ^ 126) /
          (DENv v t : Real) := by
      rw [div_add_div_same, le_div_iff₀ hDR]; nlinarith [hiR, hDR]
    rw [mul_div_assoc] at hstep
    linarith [hstep, jitter_over_budget_neg hx hC hC0 htneg]
  -- link 2 (free): Qv ≤ NE/DE
  obtain ⟨hgran1, _⟩ := gran_under_pair hx hC hC0 htneg
  -- link 3: NE/DE ≤ Et·Mpp with Et ≤ 1
  have hcertlo := certLo_real_neg htneg htdom
  set Et := Real.exp ((t : Real) / (2 ^ 128 : Real)) with hEtdef
  set NE := evalPoly ExpCertV.numExpV t with hNEdef
  set DE := evalPoly ExpCertV.denExpV t with hDEdef2
  set Mpp : Real := ((2 ^ 131 : Real) + 1) / (2 ^ 131 : Real) with hMppdef
  have hNEDE_le : (NE : Real) / (DE : Real) ≤ Et * Mpp := by
    have hc : ((2 ^ 131 : Int) : Real) * (NE : Real) /
        (((2 ^ 131 + 1 : Int) : Real) * (DE : Real)) ≤ Et := hcertlo
    rw [hMppdef]
    have key : (NE : Real) / (DE : Real) =
        (((2 ^ 131 : Real) + 1) / (2 ^ 131 : Real)) *
          (((2 ^ 131 : Int) : Real) * (NE : Real) /
            (((2 ^ 131 + 1 : Int) : Real) * (DE : Real))) := by
      push_cast; field_simp; ring
    rw [key, mul_comm Et _]; exact mul_le_mul_of_nonneg_left hc (by positivity)
  have hEt_le_one : Et ≤ 1 := by
    rw [hEtdef, show (1:Real) = Real.exp 0 from (Real.exp_zero).symm]
    apply Real.exp_le_exp.mpr
    have htR : (t : Real) ≤ 0 := by exact_mod_cast htneg
    apply div_nonpos_of_nonpos_of_nonneg htR (by positivity)
  have hEtnn : (0:Real) ≤ Et := le_of_lt (Real.exp_pos _)
  have hMpp1 : Mpp - 1 = 1 / (2 ^ 131 : Real) := by rw [hMppdef]; field_simp
  have hcMp : (2 ^ 126 : Real) * Et * (Mpp - 1) ≤ 441941738241592203 / 10000000000000000000 := by
    rw [hMpp1]
    have h1 : (2 ^ 126 : Real) * Et * (1 / (2 ^ 131 : Real)) ≤
        (2 ^ 126 : Real) * 1 * (1 / (2 ^ 131 : Real)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hEt_le_one (by positivity)
    have hn : (2 ^ 126 : Real) * 1 * (1 / (2 ^ 131 : Real)) ≤
        441941738241592203 / 10000000000000000000 := by norm_num
    linarith [h1, hn]
  -- link 4 with Et ≤ 1
  set Ert := Real.exp (reducedArg x) with hErtdef
  have hgapover := reducedArg_close_over hx hC hC0
  have hExp_diff : Et - Ert ≤ ((t : Real) / (2 ^ 128 : Real) - reducedArg x) * Et := exp_diff_le _ _
  have hcGap1 : (2 ^ 126 : Real) * (Et - Ert) ≤ 110485434560398051 / 10000000000000000000 := by
    have h1 : Et - Ert ≤ (1 / (32 * (2 ^ 128 : Real))) * Et :=
      le_trans hExp_diff (mul_le_mul_of_nonneg_right (le_of_lt hgapover) hEtnn)
    have h2 : (2 ^ 126 : Real) * (Et - Ert) ≤ (2 ^ 126 : Real) * ((1 / (32 * (2 ^ 128 : Real))) * Et) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (2 ^ 126 : Real) * ((1 / (32 * (2 ^ 128 : Real))) * Et) ≤
        (2 ^ 126 : Real) * ((1 / (32 * (2 ^ 128 : Real))) * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEt_le_one (by positivity)) (by positivity)
    have h4 : (2 ^ 126 : Real) * ((1 / (32 * (2 ^ 128 : Real))) * 1) ≤
        110485434560398051 / 10000000000000000000 := by norm_num
    linarith [h2, h3, h4]
  -- assemble
  have hNEMp : (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) ≤
      (2 ^ 126 : Real) * Et + (2 ^ 126 : Real) * Et * (Mpp - 1) := by
    have h := mul_le_mul_of_nonneg_left hNEDE_le (by positivity : (0:Real) ≤ (2 ^ 126 : Real))
    nlinarith [h]
  have hEtErt : (2 ^ 126 : Real) * Et ≤ (2 ^ 126 : Real) * Ert +
      110485434560398051 / 10000000000000000000 := by nlinarith [hcGap1]
  have hgranR : (2 ^ 126 : Real) * ((NUMv v t : Real) / (DENv v t : Real)) ≤
      (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) :=
    mul_le_mul_of_nonneg_left hgran1 (by positivity)
  calc (r0 : Real) ≤ (2 ^ 126 : Real) * ((NUMv v t : Real) / (DENv v t : Real)) +
        6207065162659510332 / 10000000000000000000 := hlink1
    _ ≤ (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) +
        6207065162659510332 / 10000000000000000000 := by linarith [hgranR]
    _ ≤ ((2 ^ 126 : Real) * Et + 441941738241592203 / 10000000000000000000) +
        6207065162659510332 / 10000000000000000000 := by linarith [hNEMp, hcMp]
    _ ≤ (((2 ^ 126 : Real) * Ert + 110485434560398051 / 10000000000000000000) +
          441941738241592203 / 10000000000000000000) +
        6207065162659510332 / 10000000000000000000 := by linarith [hEtErt]
    _ ≤ (2 ^ 126 : Real) * Real.exp (reducedArg x) +
        10050013498897899168 / 10000000000000000000 := by
        rw [hErtdef]
        have : (110485434560398051 : Real) / 10000000000000000000 +
            441941738241592203 / 10000000000000000000 +
            6207065162659510332 / 10000000000000000000 ≤
            10050013498897899168 / 10000000000000000000 := by norm_num
        linarith [this]

/-- **Per-point never-over (tight, any sign):** `r0 ≤ 2¹²⁶·exp(rt) + B` (`WAD·B < MARGIN`). -/
theorem r0_real_over_within {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (int256 (r0Tree x) : Real) ≤ (2 ^ 126 : Real) * Real.exp (reducedArg x) +
      10050013498897899168 / 10000000000000000000 := by
  rcases le_or_gt 0 (int256 (tTree x)) with htnn | htneg
  · exact r0_real_over_tight hx hC hC0 htnn
  · exact r0_real_over_tight_neg hx hC hC0 (le_of_lt htneg)

/-! ## The octave real identity `E·2^(108−k) = WAD·2¹⁰⁸·exp(rt)`

The target `E = WAD·exp(X/RAY)`. With `rt = X/RAY − k·ln2` the reduced argument, `exp(X/RAY) =
exp(rt)·2^k`, so the closing-shift fold `E·2^(108−k) = WAD·2¹⁰⁸·exp(rt)` (and `WAD·2¹⁰⁸ = 5¹⁸·2¹²⁶`,
the `5¹⁸·2¹⁰⁸` output grid's image of the Q126 quotient). This collapses the never-over/deficit
inequalities (stated against `E·2^s`, `s = 108 − k`) onto the clean octave-independent relation
`r0 ≈ 2¹²⁶·exp(rt)`. -/

/-- `exp(X/RAY) = exp(rt)·2^k` (`k = int256 (kTree x)`, possibly negative; `2^k` is a real `zpow`). -/
theorem exp_X_over_RAY (x : Nat) :
    Real.exp ((int256 x : Real) / (10 ^ 27 : Real)) =
      Real.exp (reducedArg x) * (2 : Real) ^ (int256 (kTree x)) := by
  have hlog : Real.exp ((int256 (kTree x) : Real) * Real.log 2) = (2 : Real) ^ (int256 (kTree x)) := by
    rw [← Real.rpow_intCast 2 (int256 (kTree x)),
      Real.rpow_def_of_pos (by norm_num : (0:Real) < 2), mul_comm]
  rw [show (int256 x : Real) / (10 ^ 27 : Real) =
        reducedArg x + (int256 (kTree x) : Real) * Real.log 2 from by
      unfold reducedArg; ring,
    Real.exp_add, hlog]

/-- **The octave fold of the target.** `E·2^(108−k) = WAD·2¹⁰⁸·exp(rt)`, with `s = 108 − k` the
closing shift. -/
theorem target_octave_fold {x : Nat} (s : Nat) (hs : (s : Int) = 108 - int256 (kTree x)) :
    expRayToWadTarget (int256 x) * (2 ^ s : Real) =
      (WAD : Real) * (2 ^ 108 : Real) * Real.exp (reducedArg x) := by
  unfold expRayToWadTarget
  rw [show (RAY : Real) = (10 ^ 27 : Real) from by unfold RAY; norm_num, exp_X_over_RAY x]
  -- 2^k · 2^s = 2^108 with k+s = 108 (k : Int, s : Nat).
  set k := int256 (kTree x) with hkdef
  have hks : k + (s : Int) = 108 := by omega
  have hpow : (2 : Real) ^ k * (2 : Real) ^ (s : Nat) = (2 : Real) ^ (108 : Nat) := by
    rw [show ((2 : Real) ^ (s : Nat)) = (2 : Real) ^ (s : Int) from by
      rw [zpow_natCast], ← zpow_add₀ (by norm_num : (2:Real) ≠ 0), hks]
    norm_num
  rw [show ((2 ^ s : Real)) = (2 : Real) ^ (s : Nat) from by norm_num]
  calc (WAD : Real) * (Real.exp (reducedArg x) * (2 : Real) ^ k) * (2 : Real) ^ (s : Nat)
      = (WAD : Real) * ((2 : Real) ^ k * (2 : Real) ^ (s : Nat)) * Real.exp (reducedArg x) := by ring
    _ = (WAD : Real) * (2 ^ 108 : Real) * Real.exp (reducedArg x) := by
          rw [hpow]

end

end ExpYul
