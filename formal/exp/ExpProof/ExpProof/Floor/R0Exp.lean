import ExpProof.Floor.R0Bound
import ExpProof.Floor.CapsV
import ExpProof.Floor.Reduce
import ExpProof.Mono.Quot
import ExpProof.Mono.Cross
import Common.Seam.RealExpBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The per-point `r0`-vs-`exp` bridge

This module brackets the Q126 quotient `r0Tree x` against `2¹²⁶·exp(rt)` (`rt = X/RAY − k·ln2` the
reduced argument), the single content left for `RuntimeR0Bound`/`SeamR0Bound`. It chains:

* the **v-truncation** `evNumV(vTree x)·2⁶⁴⁰ ≤ evalPoly evNumVPoly t < evNumV(vTree x)·2⁶⁴⁰ + 2¹¹⁹³`
  (the cert polynomial in `t` uses the exact `v = t²/2¹²⁸`; the gap-2 bridge uses the truncated
  `vTree x = ⌊t²/2¹²⁸⌋`; one `v`-step of the monotone Horner polynomial is below `2⁵⁵³`);
* the **gap-2 Horner-truncation bridge** (`evTree_bracket`/`odTree_bracket`, already proven);
* the **`sdiv` floor** `r0·den ≤ 2¹²⁶·num < (r0+1)·den`;
* the **v-form cert** (`CapsV`) `exp(t/2¹²⁸) ≈ ê_v` within a dyadic margin;
* the **reduced-argument bound** (`Reduce`) `|rt − t/2¹²⁸| < 2/2¹²⁸`.

The net envelope `r0Tree x ∈ (2¹²⁶·exp(rt) − C₋, 2¹²⁶·exp(rt) + C₊)` is what the `MARGIN`-absorbing
`over`/`under`/seam inequalities consume.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Poly

set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

/-! ## The even/odd Horner polynomials in `w = t²` and the cert-polynomial bridge -/

/-- The even Horner polynomial in `w` (degree 5, monic), at the cleared scale `2¹¹⁹³`. -/
def Pev : List Int :=
  [0x4e14a45e8ec305e233e11b4174e214ac * 2 ^ 1193,
   0x93f11e65781741b92fa7fc4f4fffcca2 * 2 ^ 933,
   0x9064d965e1c4863b73604e0ddbec53f9 * 2 ^ 671,
   0x9a036222e11aee18465042f8ea64c8 * 2 ^ 415,
   0xb9aacfad41060587203a79af0ebc * 2 ^ 157,
   1]

/-- The odd Horner polynomial in `w` (degree 4), at the cleared scale `2¹⁰⁴²`. -/
def Pod : List Int :=
  [0x270a522f476182f119f08da0ba710a56 * 2 ^ 1042,
   0xaf5662483c4ce783a9ef5fe025f42e9e * 2 ^ 779,
   0xad4506b00b1246c7e5b4fd33e1201b * 2 ^ 524,
   0xc926ddbf3830ca5561cc01585402d0 * 2 ^ 259,
   0xdc07aff85e5bb5629d0fb64a84bb]

/-- `evNumVPoly(t) = Pev(t²)`: the cert even polynomial is `Pev` composed with squaring. -/
theorem evNumVPoly_eq_Pev_sq (t : Int) :
    evalPoly ExpCertV.evNumVPoly t = evalPoly Pev (t ^ 2) := by
  unfold ExpCertV.evNumVPoly ExpCertV.mulT2 Pev
  simp only [evalPoly_polyAdd, evalPoly_polyScale, evalPoly]
  ring

/-- `odNumVPoly(t) = Pod(t²)`. -/
theorem odNumVPoly_eq_Pod_sq (t : Int) :
    evalPoly ExpCertV.odNumVPoly t = evalPoly Pod (t ^ 2) := by
  unfold ExpCertV.odNumVPoly ExpCertV.mulT2 Pod
  simp only [evalPoly_polyAdd, evalPoly_polyScale, evalPoly]
  ring

/-- `Pev(2¹²⁸·v) = evNumV(v)·2⁶⁴⁰` — the `w`-polynomial at the grid point `w = 2¹²⁸·v` recovers the
integer even-Horner accumulator (scaled). -/
theorem Pev_grid (v : Nat) : evalPoly Pev (2 ^ 128 * (v : Int)) = (evNumV v : Int) * 2 ^ 640 := by
  unfold Pev evNumV
  simp only [evalPoly]
  push_cast
  ring

/-- `Pod(2¹²⁸·v) = odNumV(v)·2⁵¹²`. -/
theorem Pod_grid (v : Nat) : evalPoly Pod (2 ^ 128 * (v : Int)) = (odNumV v : Int) * 2 ^ 512 := by
  unfold Pod odNumV
  simp only [evalPoly]
  push_cast
  ring

/-! ## Monotonicity of the `w`-polynomials and the single-`v`-step bound -/

/-- A polynomial with nonnegative coefficients evaluates nonnegatively on the nonnegative domain. -/
theorem evalPoly_nonneg_of_nonneg {p : List Int} (hp : ∀ c ∈ p, 0 ≤ c) {a : Int} (ha : 0 ≤ a) :
    0 ≤ evalPoly p a := by
  induction p with
  | nil => simp [evalPoly]
  | cons c cs ih =>
    have hc : 0 ≤ c := hp c List.mem_cons_self
    have hcs : ∀ d ∈ cs, 0 ≤ d := fun d hd => hp d (List.mem_cons_of_mem c hd)
    simp only [evalPoly]
    exact Int.add_nonneg hc (Int.mul_nonneg ha (ih hcs))

/-- A polynomial with nonnegative coefficients is monotone on the nonnegative domain. -/
theorem evalPoly_mono_of_nonneg {p : List Int} (hp : ∀ c ∈ p, 0 ≤ c) {a b : Int}
    (ha : 0 ≤ a) (hab : a ≤ b) : evalPoly p a ≤ evalPoly p b := by
  induction p with
  | nil => simp [evalPoly]
  | cons c cs ih =>
    have hcs : ∀ d ∈ cs, 0 ≤ d := fun d hd => hp d (List.mem_cons_of_mem c hd)
    have hih := ih hcs
    have hb : 0 ≤ b := le_trans ha hab
    have hcsnn : 0 ≤ evalPoly cs a := evalPoly_nonneg_of_nonneg hcs ha
    simp only [evalPoly]
    have h1 : a * evalPoly cs a ≤ b * evalPoly cs b := by
      calc a * evalPoly cs a ≤ b * evalPoly cs a :=
            mul_le_mul_of_nonneg_right hab hcsnn
        _ ≤ b * evalPoly cs b := mul_le_mul_of_nonneg_left hih hb
    linarith [h1]

theorem Pev_coeffs_nonneg : ∀ c ∈ Pev, (0 : Int) ≤ c := by
  unfold Pev; intro c hc; fin_cases hc <;> positivity

theorem Pod_coeffs_nonneg : ∀ c ∈ Pod, (0 : Int) ≤ c := by
  unfold Pod; intro c hc; fin_cases hc <;> positivity

/-- `Pev` is monotone on the nonnegative domain. -/
theorem Pev_mono {a b : Int} (ha : 0 ≤ a) (hab : a ≤ b) :
    evalPoly Pev a ≤ evalPoly Pev b := evalPoly_mono_of_nonneg Pev_coeffs_nonneg ha hab

/-- `Pod` is monotone on the nonnegative domain. -/
theorem Pod_mono {a b : Int} (ha : 0 ≤ a) (hab : a ≤ b) :
    evalPoly Pod a ≤ evalPoly Pod b := evalPoly_mono_of_nonneg Pod_coeffs_nonneg ha hab

/-- The odd cert polynomial `odNumVPoly` is nonnegative everywhere (`= Pod(t²)`, nonneg coeffs). -/
theorem odNumVPoly_nonneg (t : Int) : 0 ≤ evalPoly ExpCertV.odNumVPoly t := by
  rw [odNumVPoly_eq_Pod_sq]
  exact evalPoly_nonneg_of_nonneg Pod_coeffs_nonneg (by positivity)

/-- One `v`-step of the even Horner polynomial is below `2⁵⁴⁹ = 2⁵⁵³/16` for `v < 2¹²⁶` (the step is
`≈ 0.036·2⁵⁵³` at the band top; the dyadic `2⁵⁴⁹` leaves comfortable headroom). The tightness here
feeds the joint `over` budget. -/
theorem evNumV_step {v : Nat} (hv : v < 2 ^ 126) :
    (evNumV (v + 1) : Int) - (evNumV v : Int) < 2 ^ 549 := by
  unfold evNumV
  push_cast
  have hvle : (v : Int) < 2 ^ 126 := by exact_mod_cast hv
  have hvnn : (0 : Int) ≤ (v : Int) := Int.natCast_nonneg _
  nlinarith [hvle, hvnn, mul_nonneg hvnn hvnn, Int.mul_nonneg hvnn (Int.mul_nonneg hvnn hvnn),
    Int.mul_nonneg (Int.mul_nonneg hvnn hvnn) (Int.mul_nonneg hvnn hvnn)]

/-- One `v`-step of the odd Horner polynomial is below `2⁵²⁵ = 2⁵³⁰/32` for `v < 2¹²⁶`. -/
theorem odNumV_step {v : Nat} (hv : v < 2 ^ 126) :
    (odNumV (v + 1) : Int) - (odNumV v : Int) < 2 ^ 525 := by
  unfold odNumV
  push_cast
  have hvle : (v : Int) < 2 ^ 126 := by exact_mod_cast hv
  have hvnn : (0 : Int) ≤ (v : Int) := Int.natCast_nonneg _
  nlinarith [hvle, hvnn, mul_nonneg hvnn hvnn, Int.mul_nonneg hvnn (Int.mul_nonneg hvnn hvnn)]

/-! ## The cert polynomial brackets the runtime accumulator (gap-2 ∘ v-truncation) -/

/-- The squared reduced argument splits as `t² = 2¹²⁸·vTree x + r` with `0 ≤ r < 2¹²⁸`. -/
theorem tsq_split {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    2 ^ 128 * (vTree x : Int) ≤ (int256 (tTree x)) ^ 2 ∧
      (int256 (tTree x)) ^ 2 < 2 ^ 128 * (vTree x : Int) + 2 ^ 128 := by
  obtain ⟨hveq, _⟩ := vTree_eq hx hC hC0
  have hsqnn : (0 : Int) ≤ (int256 (tTree x)) ^ 2 := sq_nonneg _
  have hdm := Int.ediv_add_emod ((int256 (tTree x)) ^ 2) (2 ^ 128)
  have hmod_lt := Int.emod_lt_of_pos ((int256 (tTree x)) ^ 2) (by norm_num : (0:Int) < 2 ^ 128)
  have hmod_nn := Int.emod_nonneg ((int256 (tTree x)) ^ 2) (by norm_num : (2:Int) ^ 128 ≠ 0)
  rw [hveq]
  constructor
  · nlinarith [hdm, hmod_nn]
  · nlinarith [hdm, hmod_lt]

/-- **The even cert polynomial brackets the runtime even accumulator** (gap-2 ∘ v-truncation):
`2¹¹⁹³·evTree x ≤ evalPoly evNumVPoly t < 2¹¹⁹³·evTree x + 1130577·2¹¹⁷³` (the fractional gap-2 width
`1065041·2¹¹⁷³` plus one tight v-step `2¹¹⁸⁹ = 2¹⁶·2¹¹⁷³`, summing to `1130577·2¹¹⁷³ ≈ 1.078·2¹¹⁹³`). -/
theorem evNumVPoly_bracket {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    2 ^ 1193 * (evTree x : Int) ≤ evalPoly ExpCertV.evNumVPoly (int256 (tTree x)) ∧
      evalPoly ExpCertV.evNumVPoly (int256 (tTree x)) <
        2 ^ 1193 * (evTree x : Int) + 1130577 * 2 ^ 1173 := by
  obtain ⟨_, hvlt⟩ := vTree_eq hx hC hC0
  obtain ⟨hg2lo, hg2hi⟩ := evTree_bracket hvlt
  obtain ⟨hsqlo, hsqhi⟩ := tsq_split hx hC hC0
  set t := int256 (tTree x) with htdef
  have hsqnn : (0 : Int) ≤ t ^ 2 := sq_nonneg _
  have hgridnn : (0 : Int) ≤ 2 ^ 128 * (vTree x : Int) := mul_nonneg (by norm_num) (Int.natCast_nonneg _)
  -- v-truncation: Pev(2^128·vTree) ≤ Pev(t²) ≤ Pev(2^128·vTree + 2^128) (monotone)
  have hmono_lo : evalPoly Pev (2 ^ 128 * (vTree x : Int)) ≤ evalPoly Pev (t ^ 2) :=
    Pev_mono hgridnn hsqlo
  have hmono_hi : evalPoly Pev (t ^ 2) ≤ evalPoly Pev (2 ^ 128 * ((vTree x + 1 : Nat) : Int)) := by
    apply Pev_mono hsqnn
    push_cast; linarith [hsqhi]
  rw [evNumVPoly_eq_Pev_sq]
  rw [Pev_grid] at hmono_lo
  rw [Pev_grid (vTree x + 1)] at hmono_hi
  -- gap-2: evNumV(vTree)·2^640 ≥ 2^553·evTree·2^640 = 2^1193·evTree
  have hg2lo' : 2 ^ 1193 * (evTree x : Int) ≤ (evNumV (vTree x) : Int) * 2 ^ 640 := by
    have h : (2 ^ 553 * evTree x : Nat) ≤ evNumV (vTree x) := hg2lo
    have : (2 ^ 553 * evTree x : Int) ≤ (evNumV (vTree x) : Int) := by exact_mod_cast h
    nlinarith [this]
  -- gap-2 hi (fractional): evNumV(vTree)·2^640 < 2^1193·evTree + 1065041·2^1173
  have hg2hi' : (evNumV (vTree x) : Int) * 2 ^ 640 < 2 ^ 1193 * (evTree x : Int) + 1065041 * 2 ^ 1173 := by
    have h : evNumV (vTree x) < 2 ^ 553 * evTree x + 1065041 * 2 ^ 533 := hg2hi
    have : (evNumV (vTree x) : Int) < (2 ^ 553 * evTree x + 1065041 * 2 ^ 533 : Nat) := by exact_mod_cast h
    push_cast at this; nlinarith [this]
  -- tight v-step: evNumV(vTree+1)·2^640 < evNumV(vTree)·2^640 + 2^549·2^640 = … + 2^1189
  have hstep := evNumV_step hvlt
  have hstep' : (evNumV (vTree x + 1) : Int) * 2 ^ 640 < (evNumV (vTree x) : Int) * 2 ^ 640 + 2 ^ 1189 := by
    have he : (2:Int) ^ 1189 = 2 ^ 549 * 2 ^ 640 := by rw [← pow_add]
    rw [he]; nlinarith [hstep, pow_pos (by norm_num : (0:Int) < 2) 640]
  refine ⟨le_trans hg2lo' hmono_lo, ?_⟩
  calc evalPoly Pev (t ^ 2) ≤ (evNumV (vTree x + 1) : Int) * 2 ^ 640 := hmono_hi
    _ < (evNumV (vTree x) : Int) * 2 ^ 640 + 2 ^ 1189 := hstep'
    _ < 2 ^ 1193 * (evTree x : Int) + 1065041 * 2 ^ 1173 + 2 ^ 1189 := by linarith [hg2hi']
    _ = 2 ^ 1193 * (evTree x : Int) + 1130577 * 2 ^ 1173 := by
          rw [show (2:Int) ^ 1189 = 2 ^ 16 * 2 ^ 1173 from by rw [← pow_add]]; ring

/-- **The odd cert polynomial brackets the runtime odd accumulator** (gap-2 ∘ v-truncation):
`2¹⁰⁴²·odTree x ≤ evalPoly odNumVPoly t < 2¹⁰⁴²·odTree x + 69402657·2¹⁰¹⁶` (the fractional gap-2
width `67305505·2¹⁰¹⁶` plus one tight v-step `2¹⁰³⁷ = 2²¹·2¹⁰¹⁶`, summing to `≈ 1.003·2¹⁰⁴²`). -/
theorem odNumVPoly_bracket {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    2 ^ 1042 * (odTree x : Int) ≤ evalPoly ExpCertV.odNumVPoly (int256 (tTree x)) ∧
      evalPoly ExpCertV.odNumVPoly (int256 (tTree x)) <
        2 ^ 1042 * (odTree x : Int) + 69402657 * 2 ^ 1016 := by
  obtain ⟨_, hvlt⟩ := vTree_eq hx hC hC0
  obtain ⟨hg2lo, hg2hi⟩ := odTree_bracket hvlt
  obtain ⟨hsqlo, hsqhi⟩ := tsq_split hx hC hC0
  set t := int256 (tTree x) with htdef
  have hsqnn : (0 : Int) ≤ t ^ 2 := sq_nonneg _
  have hgridnn : (0 : Int) ≤ 2 ^ 128 * (vTree x : Int) := mul_nonneg (by norm_num) (Int.natCast_nonneg _)
  have hmono_lo : evalPoly Pod (2 ^ 128 * (vTree x : Int)) ≤ evalPoly Pod (t ^ 2) :=
    Pod_mono hgridnn hsqlo
  have hmono_hi : evalPoly Pod (t ^ 2) ≤ evalPoly Pod (2 ^ 128 * ((vTree x + 1 : Nat) : Int)) := by
    apply Pod_mono hsqnn
    push_cast; linarith [hsqhi]
  rw [odNumVPoly_eq_Pod_sq]
  rw [Pod_grid] at hmono_lo
  rw [Pod_grid (vTree x + 1)] at hmono_hi
  have hg2lo' : 2 ^ 1042 * (odTree x : Int) ≤ (odNumV (vTree x) : Int) * 2 ^ 512 := by
    have h : (2 ^ 530 * odTree x : Nat) ≤ odNumV (vTree x) := hg2lo
    have : (2 ^ 530 * odTree x : Int) ≤ (odNumV (vTree x) : Int) := by exact_mod_cast h
    nlinarith [this]
  have hg2hi' : (odNumV (vTree x) : Int) * 2 ^ 512 < 2 ^ 1042 * (odTree x : Int) + 67305505 * 2 ^ 1016 := by
    have h : odNumV (vTree x) < 2 ^ 530 * odTree x + 67305505 * 2 ^ 504 := hg2hi
    have : (odNumV (vTree x) : Int) < (2 ^ 530 * odTree x + 67305505 * 2 ^ 504 : Nat) := by exact_mod_cast h
    push_cast at this; nlinarith [this]
  have hstep := odNumV_step hvlt
  have hstep' : (odNumV (vTree x + 1) : Int) * 2 ^ 512 < (odNumV (vTree x) : Int) * 2 ^ 512 + 2 ^ 1037 := by
    have he : (2:Int) ^ 1037 = 2 ^ 525 * 2 ^ 512 := by rw [← pow_add]
    rw [he]; nlinarith [hstep, pow_pos (by norm_num : (0:Int) < 2) 512]
  refine ⟨le_trans hg2lo' hmono_lo, ?_⟩
  calc evalPoly Pod (t ^ 2) ≤ (odNumV (vTree x + 1) : Int) * 2 ^ 512 := hmono_hi
    _ < (odNumV (vTree x) : Int) * 2 ^ 512 + 2 ^ 1037 := hstep'
    _ < 2 ^ 1042 * (odTree x : Int) + 67305505 * 2 ^ 1016 + 2 ^ 1037 := by linarith [hg2hi']
    _ = 2 ^ 1042 * (odTree x : Int) + 69402657 * 2 ^ 1016 := by
          rw [show (2:Int) ^ 1037 = 2 ^ 21 * 2 ^ 1016 from by rw [← pow_add]]; ring

/-! ## The `t·Od` term and the numerator/denominator brackets (nonnegative half `t ≥ 0`) -/

/-- `evalPoly todNumV t = 2²³ · t · evalPoly odNumVPoly t`. -/
theorem evalTodNumV (t : Int) :
    evalPoly ExpCertV.todNumV t = 2 ^ 23 * (t * evalPoly ExpCertV.odNumVPoly t) := by
  unfold ExpCertV.todNumV
  rw [evalPoly_polyScale]
  simp only [evalPoly]
  ring

/-- `evalPoly numExpV t = evalPoly evNumVPoly t + evalPoly todNumV t`. -/
theorem evalNumExpV (t : Int) :
    evalPoly ExpCertV.numExpV t = evalPoly ExpCertV.evNumVPoly t + evalPoly ExpCertV.todNumV t := by
  unfold ExpCertV.numExpV; rw [evalPoly_polyAdd]

/-- `evalPoly denExpV t = evalPoly evNumVPoly t − evalPoly todNumV t`. -/
theorem evalDenExpV (t : Int) :
    evalPoly ExpCertV.denExpV t = evalPoly ExpCertV.evNumVPoly t - evalPoly ExpCertV.todNumV t := by
  unfold ExpCertV.denExpV; rw [evalPoly_polySub]

/-- `evNumVPoly` is even (`= Pev(t²)`). -/
theorem evNumVPoly_even (t : Int) :
    evalPoly ExpCertV.evNumVPoly (-t) = evalPoly ExpCertV.evNumVPoly t := by
  rw [evNumVPoly_eq_Pev_sq, evNumVPoly_eq_Pev_sq]
  congr 1; ring

/-- `todNumV` is odd (`= 2²³·t·Pod(t²)`). -/
theorem todNumV_odd (t : Int) :
    evalPoly ExpCertV.todNumV (-t) = -evalPoly ExpCertV.todNumV t := by
  rw [evalTodNumV, evalTodNumV, odNumVPoly_eq_Pod_sq, odNumVPoly_eq_Pod_sq]
  rw [show ((-t)^2 : Int) = t^2 from by ring]
  ring

/-- **Reciprocal symmetry** `numExpV(−t) = denExpV(t)` and `denExpV(−t) = numExpV(t)`. -/
theorem numExpV_neg_eq_denExpV (t : Int) :
    evalPoly ExpCertV.numExpV (-t) = evalPoly ExpCertV.denExpV t := by
  rw [evalNumExpV, evalDenExpV, evNumVPoly_even, todNumV_odd]; ring

theorem denExpV_neg_eq_numExpV (t : Int) :
    evalPoly ExpCertV.denExpV (-t) = evalPoly ExpCertV.numExpV t := by
  rw [evalDenExpV, evalNumExpV, evNumVPoly_even, todNumV_odd]; ring

/-- **The `t·Od` cert term brackets the runtime `tod`** (nonnegative half): for `0 ≤ t`,
`2¹¹⁹³·tod ≤ evalPoly todNumV t < 2¹¹⁹³·tod + 2⁵·2¹¹⁹³`. -/
theorem todNumV_bracket {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    2 ^ 1193 * (int256 (todTree x)) ≤ evalPoly ExpCertV.todNumV (int256 (tTree x)) ∧
      evalPoly ExpCertV.todNumV (int256 (tTree x)) < 2 ^ 1193 * (int256 (todTree x)) + 4 * 2 ^ 1193 := by
  obtain ⟨_, _, htodlo, htodhi⟩ := todTree_bound hx hC hC0
  obtain ⟨hodlo, hodhi⟩ := odNumVPoly_bracket hx hC hC0
  set t := int256 (tTree x) with htdef
  rw [evalTodNumV]
  -- odTree ≥ 0
  have hodnn : (0 : Int) ≤ (odTree x : Int) := Int.natCast_nonneg _
  -- 2^128·tod ≤ t·odTree < 2^128·tod + 2^128
  -- multiply odd bracket by t·2^23 (t ≥ 0):
  have hmul_lo : t * (2 ^ 1042 * (odTree x : Int)) ≤ t * evalPoly ExpCertV.odNumVPoly t :=
    mul_le_mul_of_nonneg_left hodlo htnn
  have hmul_hi : t * evalPoly ExpCertV.odNumVPoly t ≤ t * (2 ^ 1042 * (odTree x : Int) + 69402657 * 2 ^ 1016) :=
    mul_le_mul_of_nonneg_left (le_of_lt hodhi) htnn
  -- tod·2^128 ≤ t·odTree and t·odTree < tod·2^128 + 2^128
  have htod_lo : (2 ^ 128 : Int) * (int256 (todTree x)) ≤ t * (odTree x : Int) := htodlo
  have htod_hi : t * (odTree x : Int) < (2 ^ 128 : Int) * (int256 (todTree x)) + 2 ^ 128 := htodhi
  constructor
  · -- 2^1193·tod ≤ 2^23·(t·odpoly).  2^1193·tod = 2^23·(2^1042·(2^128·tod)) ... use 2^1193=2^23·2^1042·2^128
    have key : 2 ^ 1193 * (int256 (todTree x)) ≤ 2 ^ 23 * (t * (2 ^ 1042 * (odTree x : Int))) := by
      have e : (2 : Int) ^ 23 * (2 ^ 1042 * ((2:Int) ^ 128 * (int256 (todTree x)))) =
          2 ^ 1193 * (int256 (todTree x)) := by ring
      rw [← e]
      have := mul_le_mul_of_nonneg_left htod_lo (by positivity : (0:Int) ≤ 2 ^ 23 * 2 ^ 1042)
      nlinarith [this]
    calc 2 ^ 1193 * (int256 (todTree x)) ≤ 2 ^ 23 * (t * (2 ^ 1042 * (odTree x : Int))) := key
      _ ≤ 2 ^ 23 * (t * evalPoly ExpCertV.odNumVPoly t) :=
          mul_le_mul_of_nonneg_left hmul_lo (by positivity)
  · -- 2^23·(t·odpoly) < 2^1193·tod + 4·2^1193 (the tight odd width 69402657·2^1016·t stays well under)
    -- t·odpoly ≤ 2^1042·(t·odTree) + 69402657·2^1016·t, t·odTree < 2^128·tod + 2^128, t < 2^128.
    obtain ⟨htlo', hthi'⟩ := tTree_bound hx hC hC0
    have htlt : t < 2 ^ 128 := by
      have : t < 2 ^ 127 := by rw [show ((2:Int)^127) = 170141183460469231731687303715884105728 from by norm_num]; exact hthi'
      have : (2:Int)^127 < 2 ^ 128 := by norm_num
      omega
    have key : 2 ^ 23 * (t * evalPoly ExpCertV.odNumVPoly t) <
        2 ^ 1193 * (int256 (todTree x)) + 4 * 2 ^ 1193 := by
      have h1 : t * evalPoly ExpCertV.odNumVPoly t ≤
          2 ^ 1042 * (t * (odTree x : Int)) + 69402657 * 2 ^ 1016 * t := by
        nlinarith [hmul_hi]
      have h2 : t * (odTree x : Int) < (2 ^ 128 : Int) * (int256 (todTree x)) + 2 ^ 128 := htod_hi
      -- 2^23·69402657·2^1016·t < 69402657·2^1167 < 3·2^1193 (t < 2^128, 69402657 < 3·2^26)
      have hpow : (69402657 : Int) * 2 ^ 1167 < 3 * 2 ^ 1193 := by
        have he : (3:Int) * 2 ^ 1193 = (3 * 2 ^ 26) * 2 ^ 1167 := by
          rw [show (3:Int) * 2 ^ 26 * 2 ^ 1167 = 3 * (2 ^ 26 * 2 ^ 1167) from by ring,
            show (2:Int) ^ 26 * 2 ^ 1167 = 2 ^ (26 + 1167) from by rw [← pow_add],
            show (26:Nat) + 1167 = 1193 from by norm_num]
        rw [he]
        have : (69402657 : Int) < 3 * 2 ^ 26 := by norm_num
        nlinarith [pow_pos (by norm_num : (0:Int) < 2) 1167, this]
      have hcarry : (2:Int) ^ 23 * (69402657 * 2 ^ 1016 * t) ≤ 69402657 * 2 ^ 1167 := by
        have ht : (2:Int) ^ 23 * (69402657 * 2 ^ 1016 * t) = 69402657 * 2 ^ 1039 * t := by
          rw [show (2:Int) ^ 1039 = 2 ^ 23 * 2 ^ 1016 from by rw [← pow_add]]; ring
        rw [ht, show (2:Int) ^ 1167 = 2 ^ 1039 * 2 ^ 128 from by rw [← pow_add]]
        nlinarith [pow_pos (by norm_num : (0:Int) < 2) 1039, htlt, htnn]
      nlinarith [h1, h2, htlt, htnn, mul_nonneg htnn hodnn, hcarry, hpow]
    exact key

/-! ## The numerator/denominator cert brackets and the `r0`-vs-`ê_v` bracket -/

/-- The numerator cert polynomial brackets `2¹¹⁹³·num_rt` (`num_rt = ev + tod`): within `35·2¹¹⁹³`. -/
theorem numExpV_bracket {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    2 ^ 1193 * ((evTree x : Int) + int256 (todTree x)) ≤ evalPoly ExpCertV.numExpV (int256 (tTree x)) ∧
      evalPoly ExpCertV.numExpV (int256 (tTree x)) <
        2 ^ 1193 * ((evTree x : Int) + int256 (todTree x)) + 35 * 2 ^ 1193 := by
  obtain ⟨hevlo, hevhi⟩ := evNumVPoly_bracket hx hC hC0
  obtain ⟨htodlo, htodhi⟩ := todNumV_bracket hx hC hC0 htnn
  rw [evalNumExpV]
  constructor
  · nlinarith [hevlo, htodlo]
  · nlinarith [hevhi, htodhi]

/-- The denominator cert polynomial brackets `2¹¹⁹³·den_rt` (`den_rt = ev − tod`): within `32·2¹¹⁹³`. -/
theorem denExpV_bracket {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    2 ^ 1193 * ((evTree x : Int) - int256 (todTree x)) - 32 * 2 ^ 1193 ≤
        evalPoly ExpCertV.denExpV (int256 (tTree x)) ∧
      evalPoly ExpCertV.denExpV (int256 (tTree x)) <
        2 ^ 1193 * ((evTree x : Int) - int256 (todTree x)) + 3 * 2 ^ 1193 := by
  obtain ⟨hevlo, hevhi⟩ := evNumVPoly_bracket hx hC hC0
  obtain ⟨htodlo, htodhi⟩ := todNumV_bracket hx hC hC0 htnn
  rw [evalDenExpV]
  constructor
  · nlinarith [hevlo, htodhi]
  · nlinarith [hevhi, htodlo]

/-! ## The `sdiv` floor sandwich -/

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
    have ht125 : int256 (todTree x) < 2 ^ 125 := by
      rw [show (2:Int)^125 = 42535295865117307932921825928971026432 from by norm_num]; exact htod_hi
    nlinarith [this, ht125]
  have hshl : int256 (evmShl 0x7e num) = 2 ^ 0x7e * int256 num :=
    shl126_transport hnumw (by rw [hnumi]; omega) hnumlt128
  -- r0 = sdiv (shl 126 num) den, with both operands positive
  have hr0eq : r0Tree x = evmSdiv (evmShl 0x7e num) den := rfl
  have hshlw : evmShl 0x7e num < 2 ^ 256 := evmShl_lt _ _
  have hshlpos : 0 ≤ int256 (evmShl 0x7e num) := by rw [hshl, hnumi]; positivity
  have hdenpos' : 0 < int256 den := by rw [hdeni]; omega
  have hdiv := evmSdiv_pos_pos hshlw hdenw hshlpos hdenpos'
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

/-! ## A positive lower bound on the cert denominator -/

/-- `den_rt = ev − tod > 2¹²⁵` on the region (the even accumulator dominates `|tod|`). -/
theorem den_rt_lb {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (2 : Int) ^ 125 < (evTree x : Int) - int256 (todTree x) := by
  obtain ⟨hevlo, _⟩ := evTree_facts (vTree_eq hx hC hC0).2
  obtain ⟨htod_lo, htod_hi, _, _⟩ := todTree_bound hx hC hC0
  have hev : (0x4e14a45e8ec305e233e11b4174e214ac : Int) ≤ (evTree x : Int) := by exact_mod_cast hevlo
  have ht125 : int256 (todTree x) < 2 ^ 125 := by
    rw [show (2:Int)^125 = 42535295865117307932921825928971026432 from by norm_num]; exact htod_hi
  rw [show (0x4e14a45e8ec305e233e11b4174e214ac : Int) = 103786963415199049567855548359006885036 from by norm_num] at hev
  rw [show (2:Int)^125 = 42535295865117307932921825928971026432 from by norm_num] at ht125 ⊢
  omega

/-- The cert denominator is bounded below: `denExpV(t) > 2¹³¹⁷` on the region. -/
theorem denExpV_lb {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    (2 : Int) ^ 1317 < evalPoly ExpCertV.denExpV (int256 (tTree x)) := by
  obtain ⟨hlo, _⟩ := denExpV_bracket hx hC hC0 htnn
  have hden := den_rt_lb hx hC hC0
  -- denExpV ≥ 2^1193·den_rt − 32·2^1193 > 2^1193·2^125 − 32·2^1193 = 2^1318 − 32·2^1193 > 2^1317
  have hstep : 2 ^ 1193 * ((evTree x : Int) - int256 (todTree x)) - 32 * 2 ^ 1193 >
      2 ^ 1193 * (2 ^ 125 : Int) - 32 * 2 ^ 1193 := by
    have := mul_lt_mul_of_pos_left hden (by positivity : (0:Int) < 2 ^ 1193)
    linarith [this]
  have hnum : 2 ^ 1193 * (2 ^ 125 : Int) - 32 * 2 ^ 1193 > 2 ^ 1317 := by
    rw [show (2:Int)^1193 * 2 ^ 125 = 2 ^ 1318 from by rw [← pow_add]]
    have h18 : (2:Int)^1318 = 2 * 2 ^ 1317 := by rw [show (1318:Nat) = 1 + 1317 from rfl, pow_add]; ring
    have h93 : (2:Int)^1193 < 2 ^ 1317 := by
      apply pow_lt_pow_right₀ (by norm_num) (by norm_num)
    nlinarith [h18, h93]
  linarith [hlo, hstep, hnum]

/-! ## The `r0`-vs-cert-rational bracket (direct chain) -/

/-- **`r0Tree x` brackets `2¹²⁶·ê_v`**: `r0·denExpV < 2¹²⁶·numExpV + 49·denExpV` and
`2¹²⁶·numExpV < (r0+1)·denExpV + 700·denExpV`. The loose constants are MARGIN/seam-absorbed. -/
theorem r0_vs_certRatio {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    int256 (r0Tree x) * evalPoly ExpCertV.denExpV (int256 (tTree x)) <
        2 ^ 126 * evalPoly ExpCertV.numExpV (int256 (tTree x)) +
          49 * evalPoly ExpCertV.denExpV (int256 (tTree x)) ∧
      2 ^ 126 * evalPoly ExpCertV.numExpV (int256 (tTree x)) <
        (int256 (r0Tree x) + 1) * evalPoly ExpCertV.denExpV (int256 (tTree x)) +
          700 * evalPoly ExpCertV.denExpV (int256 (tTree x)) := by
  obtain ⟨hfloor_lo, hfloor_hi⟩ := r0_floor_sandwich hx hC hC0
  obtain ⟨hnumlo, hnumhi⟩ := numExpV_bracket hx hC hC0 htnn
  obtain ⟨hdenlo, hdenhi⟩ := denExpV_bracket hx hC hC0 htnn
  obtain ⟨hr0lo, hr0hi⟩ := r0Tree_bounds hx hC hC0
  have hdenExpV_lb := denExpV_lb hx hC hC0 htnn
  set r0 := int256 (r0Tree x) with hr0def
  set num := (evTree x : Int) + int256 (todTree x) with hnumdef
  set den := (evTree x : Int) - int256 (todTree x) with hdendef
  set NE := evalPoly ExpCertV.numExpV (int256 (tTree x)) with hNEdef
  set DE := evalPoly ExpCertV.denExpV (int256 (tTree x)) with hDEdef
  have hDEpos : (0 : Int) < DE := by
    have h : (2:Int)^1317 > 0 := by positivity
    linarith [hdenExpV_lb, h]
  have hr0pos : 0 ≤ r0 := by linarith [hr0lo]
  have hr0lt : r0 < 2 ^ 128 := hr0hi
  have hp1193 : (0 : Int) < 2 ^ 1193 := by positivity
  have hden_nn : (0 : Int) ≤ den := by
    have h := den_rt_lb hx hC hC0; rw [← hdendef] at h; positivity
  -- DE bounds vs den·2^1193 (denExpV_bracket): DE - 3·2^1193 < den·2^1193 ≤ DE + 32·2^1193
  have hden2_lo : 2 ^ 1193 * den ≤ DE + 32 * 2 ^ 1193 := by linarith [hdenlo]
  have hden2_hi : DE - 3 * 2 ^ 1193 < 2 ^ 1193 * den := by linarith [hdenhi]
  -- NE bounds (numExpV_bracket): num·2^1193 ≤ NE < num·2^1193 + 35·2^1193
  have hnum2_lo : 2 ^ 1193 * num ≤ NE := hnumlo
  have hnum2_hi : NE < 2 ^ 1193 * num + 35 * 2 ^ 1193 := hnumhi
  -- 49·DE > 49·2^1317 > 3·2^1321 ≥ 3·2^1193·r0
  have h2_1321 : (3 : Int) * 2 ^ 1193 * (2 ^ 128 : Int) = 3 * 2 ^ 1321 := by rw [mul_assoc, ← pow_add]
  have hr0_loss : 3 * 2 ^ 1193 * r0 < 49 * DE := by
    have h1 : 3 * 2 ^ 1193 * r0 < 3 * 2 ^ 1193 * 2 ^ 128 := by
      apply mul_lt_mul_of_pos_left hr0lt; positivity
    have h2 : (3 : Int) * 2 ^ 1321 < 49 * 2 ^ 1317 := by
      rw [show (1321:Nat) = 4 + 1317 from rfl, pow_add]; ring_nf; nlinarith [pow_pos (by norm_num : (0:Int)<2) 1317]
    rw [h2_1321] at h1
    linarith [h1, h2, mul_lt_mul_of_pos_left hdenExpV_lb (by norm_num : (0:Int) < 49)]
  -- 700·DE > 35·2^1319 + 32·2^1193·(r0+1)  (under loss)
  have hunder_loss : 35 * 2 ^ 126 * 2 ^ 1193 + 32 * 2 ^ 1193 * (r0 + 1) < 700 * DE := by
    have h1 : 32 * 2 ^ 1193 * (r0 + 1) < 32 * 2 ^ 1193 * (2 ^ 128 + 1) := by
      apply mul_lt_mul_of_pos_left (by linarith [hr0lt]); positivity
    have hr0p1 : (32 : Int) * 2 ^ 1193 * (2 ^ 128 + 1) < 33 * 2 ^ 1321 := by
      rw [show (1321:Nat) = 4 + 1317 from rfl, pow_add]; ring_nf
      nlinarith [pow_pos (by norm_num : (0:Int)<2) 1193, pow_pos (by norm_num : (0:Int)<2) 1317]
    have h35 : (35 : Int) * 2 ^ 126 * 2 ^ 1193 = 35 * 2 ^ 1319 := by rw [mul_assoc, ← pow_add]
    have hbound : (35 : Int) * 2 ^ 1319 + 33 * 2 ^ 1321 < 700 * 2 ^ 1317 := by
      rw [show (1319:Nat) = 2 + 1317 from rfl, show (1321:Nat) = 4 + 1317 from rfl, pow_add, pow_add]
      ring_nf; nlinarith [pow_pos (by norm_num : (0:Int)<2) 1317]
    rw [h35]
    linarith [h1, hr0p1, hbound, mul_lt_mul_of_pos_left hdenExpV_lb (by norm_num : (0:Int) < 700)]
  -- abstract the powers so the final steps stay linear in the kernel
  have hfl_lo := mul_le_mul_of_nonneg_left hfloor_lo (by positivity : (0:Int) ≤ 2 ^ 1193)
  have hfl_hi := mul_lt_mul_of_pos_left hfloor_hi hp1193
  have hnumstep := mul_le_mul_of_nonneg_left hnum2_lo (by positivity : (0:Int) ≤ 2 ^ 126)
  have hNEstep := mul_lt_mul_of_pos_left hnum2_hi (by positivity : (0:Int) < 2 ^ 126)
  have hr0den_lo := mul_le_mul_of_nonneg_left (le_of_lt hden2_hi) hr0pos
  have hr0den_hi := mul_le_mul_of_nonneg_left hden2_lo (by linarith [hr0pos] : (0:Int) ≤ r0 + 1)
  -- expand products into a common shape via ring_nf, then linarith over the atoms
  constructor
  · nlinarith [hfl_lo, hnumstep, hr0den_lo, hr0_loss, hDEpos, hp1193]
  · nlinarith [hfl_hi, hNEstep, hr0den_hi, hunder_loss, hDEpos, hp1193]

-- Joint cert-ratio over: r0·DE − 2^126·NE ≤ W_ev_int·(r0−2^126), W_ev_int = 1130577·2^1173.
-- evP = evalPoly evNumVPoly t, NE = evP + todP, DE = evP − todP.  Ee = evP − 2^1193·ev ∈ [0,W_ev).
-- todP ≥ 2^1193·tod.  Floor: r0·den ≤ 2^126·num.
theorem r0_certRatio_over_tight {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) (hr0ge : (2:Int)^126 ≤ int256 (r0Tree x)) :
    int256 (r0Tree x) * evalPoly ExpCertV.denExpV (int256 (tTree x)) -
        2 ^ 126 * evalPoly ExpCertV.numExpV (int256 (tTree x)) ≤
      1130577 * 2 ^ 1173 * (int256 (r0Tree x) - 2 ^ 126) := by
  obtain ⟨hfloor_lo, _⟩ := r0_floor_sandwich hx hC hC0
  obtain ⟨hevlo, hevhi⟩ := evNumVPoly_bracket hx hC hC0
  obtain ⟨htodlo, _⟩ := todNumV_bracket hx hC hC0 htnn
  rw [evalNumExpV, evalDenExpV]
  set r0 := int256 (r0Tree x) with hr0def
  set ev := (evTree x : Int) with hevdef
  set tod := int256 (todTree x) with htoddef
  set evP := evalPoly ExpCertV.evNumVPoly (int256 (tTree x)) with hevP
  set todP := evalPoly ExpCertV.todNumV (int256 (tTree x)) with htodP
  -- r0·(evP−todP) − 2^126·(evP+todP) = evP·(r0−2^126) − todP·(r0+2^126)
  -- ≤ (2^1193·ev + W_ev)·(r0−2^126) − 2^1193·tod·(r0+2^126)
  --   [evP ≤ 2^1193 ev + W_ev (hevhi), r0−2^126≥0; todP ≥ 2^1193 tod (htodlo), -(·)(r0+2^126)≤0]
  -- = 2^1193·[ev(r0−2^126) − tod(r0+2^126)] + W_ev·(r0−2^126)
  -- = 2^1193·[(ev−tod)·r0 − 2^126·(ev+tod)] + W_ev·(r0−2^126)
  -- = 2^1193·[den·r0 − 2^126·num] + W_ev·(r0−2^126) ≤ 0 + W_ev·(r0−2^126)  [floor]
  have hr0m : (0:Int) ≤ r0 - 2^126 := by linarith [hr0ge]
  have hr0p : (0:Int) ≤ r0 + 2^126 := by linarith [hr0ge]
  -- evP ≤ 2^1193 ev + W_ev
  have hWev : evP ≤ 2^1193 * ev + 1130577 * 2^1173 := le_of_lt hevhi
  -- bound the two terms
  have hterm1 : evP * (r0 - 2^126) ≤ (2^1193 * ev + 1130577 * 2^1173) * (r0 - 2^126) :=
    mul_le_mul_of_nonneg_right hWev hr0m
  have hterm2 : 2^1193 * tod * (r0 + 2^126) ≤ todP * (r0 + 2^126) :=
    mul_le_mul_of_nonneg_right htodlo hr0p
  -- floor: r0·den ≤ 2^126·num, i.e. den·r0 - 2^126·num ≤ 0 (den=ev-tod, num=ev+tod)
  have hfloor : r0 * (ev - tod) - 2^126 * (ev + tod) ≤ 0 := by linarith [hfloor_lo]
  -- assemble: 2^1193·(den·r0 − 2^126·num) ≤ 0
  have hfloor1193 : (2:Int)^1193 * (r0 * (ev - tod) - 2^126 * (ev + tod)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hfloor
  nlinarith [hterm1, hterm2, hfloor1193]

-- For r0 ≤ 2^126 the cert-ratio over is ≤ 0: evP·(r0−2^126) ≤ 0 and todP ≥ 0.
theorem r0_certRatio_over_small {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) (hr0le : int256 (r0Tree x) ≤ (2:Int)^126) :
    int256 (r0Tree x) * evalPoly ExpCertV.denExpV (int256 (tTree x)) -
        2 ^ 126 * evalPoly ExpCertV.numExpV (int256 (tTree x)) ≤ 0 := by
  rw [evalNumExpV, evalDenExpV]
  set r0 := int256 (r0Tree x) with hr0def
  set evP := evalPoly ExpCertV.evNumVPoly (int256 (tTree x)) with hevP
  set todP := evalPoly ExpCertV.todNumV (int256 (tTree x)) with htodP
  -- evP ≥ 0, todP ≥ 0 (nonneg half), r0−2^126 ≤ 0, r0+2^126 ≥ 0
  have hevPnn : (0:Int) ≤ evP := by
    obtain ⟨hlo, _⟩ := evNumVPoly_bracket hx hC hC0
    have : (0:Int) ≤ 2^1193 * (evTree x : Int) := mul_nonneg (by norm_num) (Int.natCast_nonneg _)
    linarith [hlo, this]
  have htodPnn : (0:Int) ≤ todP := by
    rw [htodP, evalTodNumV]
    exact mul_nonneg (by positivity) (mul_nonneg htnn (odNumVPoly_nonneg _))
  have hr0nn : (0:Int) ≤ r0 := by obtain ⟨hlo, _⟩ := r0Tree_bounds hx hC hC0; linarith [hlo]
  have hr0m : r0 - 2^126 ≤ 0 := by linarith [hr0le]
  have hr0p : (0:Int) ≤ r0 + 2^126 := by positivity
  -- r0·(evP−todP) − 2^126·(evP+todP) = evP·(r0−2^126) − todP·(r0+2^126) ≤ 0
  have h1 : evP * (r0 - 2^126) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hevPnn hr0m
  have h2 : 0 ≤ todP * (r0 + 2^126) := mul_nonneg htodPnn hr0p
  nlinarith [h1, h2]


/-! ## The negative-half integer brackets

For `t < 0` the runtime `tod = ⌊t·od/2¹²⁸⌋` is nonpositive, so the `t·Od` cert term `todNumV(t)`
(odd in `t`) is also nonpositive; multiplying the (sign-independent) odd-Horner bracket by `2²³·t < 0`
flips the inequalities. The even-Horner bracket `evNumVPoly_bracket` is sign-independent (even poly).
Assembling gives the numerator/denominator brackets and the same loose `r0`-vs-`ê_v` constants, with
the floor sandwich `r0_floor_sandwich` (itself sign-free). -/

/-- **`todNumV` bracket (negative half).** For `t ≤ 0`:
`2¹¹⁹³·tod − 4·2¹¹⁹³ < todNumV(t) < 2¹¹⁹³·tod + 2·2¹¹⁹³`. -/
theorem todNumV_bracket_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) :
    2 ^ 1193 * (int256 (todTree x)) - 4 * 2 ^ 1193 < evalPoly ExpCertV.todNumV (int256 (tTree x)) ∧
      evalPoly ExpCertV.todNumV (int256 (tTree x)) < 2 ^ 1193 * (int256 (todTree x)) + 2 * 2 ^ 1193 := by
  obtain ⟨_, _, htodlo, htodhi⟩ := todTree_bound hx hC hC0
  obtain ⟨hodlo, hodhi⟩ := odNumVPoly_bracket hx hC hC0
  obtain ⟨htlo', hthi'⟩ := tTree_bound hx hC hC0
  set t := int256 (tTree x) with htdef
  rw [evalTodNumV]
  have hodnn : (0 : Int) ≤ (odTree x : Int) := Int.natCast_nonneg _
  have hodpolynn : (0 : Int) ≤ evalPoly ExpCertV.odNumVPoly t := le_trans (by positivity) hodlo
  -- multiply odd bracket by t ≤ 0 (flips):
  have hmul_lo : t * evalPoly ExpCertV.odNumVPoly t ≤ t * (2 ^ 1042 * (odTree x : Int)) :=
    mul_le_mul_of_nonpos_left hodlo htneg
  have hmul_hi : t * (2 ^ 1042 * (odTree x : Int) + 69402657 * 2 ^ 1016) ≤ t * evalPoly ExpCertV.odNumVPoly t :=
    mul_le_mul_of_nonpos_left (le_of_lt hodhi) htneg
  have htod_lo : (2 ^ 128 : Int) * (int256 (todTree x)) ≤ t * (odTree x : Int) := htodlo
  have htod_hi : t * (odTree x : Int) < (2 ^ 128 : Int) * (int256 (todTree x)) + 2 ^ 128 := htodhi
  have htgt : -(2 ^ 128 : Int) < t := by
    have : -(2:Int)^127 < t := htlo'
    have h2 : -(2:Int)^128 < -(2:Int)^127 := by norm_num
    omega
  constructor
  · -- todNumV = 2^23·(t·odpoly) ≥ 2^1065·(t·odTree) + 69402657·2^1039·t (since t ≤ 0, the odd width
    -- contributes a negative shift) ≥ 2^1193·tod − 69402657·2^1167/... > 2^1193·tod − 4·2^1193
    have h1 : 2 ^ 1042 * (t * (odTree x : Int)) + 69402657 * 2 ^ 1016 * t ≤
        t * evalPoly ExpCertV.odNumVPoly t := by nlinarith [hmul_hi]
    have h2 : (2 ^ 128 : Int) * (int256 (todTree x)) ≤ t * (odTree x : Int) := htod_lo
    -- 2^23·69402657·2^1016·t > -69402657·2^1167 > -3·2^1193 (t > -2^128)
    have hcarry : -(69402657 * 2 ^ 1167 : Int) < (2:Int) ^ 23 * (69402657 * 2 ^ 1016 * t) := by
      have ht : (2:Int) ^ 23 * (69402657 * 2 ^ 1016 * t) = 69402657 * 2 ^ 1039 * t := by
        rw [show (2:Int) ^ 1039 = 2 ^ 23 * 2 ^ 1016 from by rw [← pow_add]]; ring
      rw [ht, show (69402657 : Int) * 2 ^ 1167 = 69402657 * 2 ^ 1039 * 2 ^ 128 from by
        rw [show (2:Int) ^ 1167 = 2 ^ 1039 * 2 ^ 128 from by rw [← pow_add]]; ring]
      nlinarith [pow_pos (by norm_num : (0:Int) < 2) 1039, htgt]
    have hpow : -(69402657 * 2 ^ 1167 : Int) ≥ -(3 * 2 ^ 1193) := by
      rw [ge_iff_le, neg_le_neg_iff, show (3:Int) * 2 ^ 1193 = (3 * 2 ^ 26) * 2 ^ 1167 from by
        rw [show (2:Int) ^ 1193 = 2 ^ 26 * 2 ^ 1167 from by rw [← pow_add]]; ring]
      have : (69402657 : Int) ≤ 3 * 2 ^ 26 := by norm_num
      nlinarith [pow_pos (by norm_num : (0:Int) < 2) 1167, this]
    nlinarith [h1, h2, htgt, hcarry, hpow]
  · -- todNumV = 2^23·(t·odpoly) ≤ 2^23·(t·2^1042 odTree) = 2^1065·(t·odTree) < 2^1193·tod + 2^1193
    have h1 : t * evalPoly ExpCertV.odNumVPoly t ≤ 2 ^ 1042 * (t * (odTree x : Int)) := by
      nlinarith [hmul_lo]
    have h2 : t * (odTree x : Int) < (2 ^ 128 : Int) * (int256 (todTree x)) + 2 ^ 128 := htod_hi
    nlinarith [h1, h2]

/-- **Numerator/denominator brackets (negative half).** `NE ∈ (S·num_rt − 4S, S·num_rt + 4S)`,
`DE ∈ (S·den_rt − 2S, S·den_rt + 4S)` (`S = 2¹¹⁹³`, `num_rt = ev + tod`, `den_rt = ev − tod`). -/
theorem numExpV_bracket_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) :
    2 ^ 1193 * ((evTree x : Int) + int256 (todTree x)) - 4 * 2 ^ 1193 <
        evalPoly ExpCertV.numExpV (int256 (tTree x)) ∧
      evalPoly ExpCertV.numExpV (int256 (tTree x)) <
        2 ^ 1193 * ((evTree x : Int) + int256 (todTree x)) + 5 * 2 ^ 1193 := by
  obtain ⟨hevlo, hevhi⟩ := evNumVPoly_bracket hx hC hC0
  obtain ⟨htodlo, htodhi⟩ := todNumV_bracket_neg hx hC hC0 htneg
  rw [evalNumExpV]
  constructor
  · nlinarith [hevlo, htodlo]
  · nlinarith [hevhi, htodhi]

theorem denExpV_bracket_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) :
    2 ^ 1193 * ((evTree x : Int) - int256 (todTree x)) - 2 * 2 ^ 1193 <
        evalPoly ExpCertV.denExpV (int256 (tTree x)) ∧
      evalPoly ExpCertV.denExpV (int256 (tTree x)) <
        2 ^ 1193 * ((evTree x : Int) - int256 (todTree x)) + 7 * 2 ^ 1193 := by
  obtain ⟨hevlo, hevhi⟩ := evNumVPoly_bracket hx hC hC0
  obtain ⟨htodlo, htodhi⟩ := todNumV_bracket_neg hx hC hC0 htneg
  rw [evalDenExpV]
  constructor
  · nlinarith [hevlo, htodhi]
  · nlinarith [hevhi, htodlo]

/-- The cert denominator stays large on the negative half too: `denExpV(t) > 2¹³¹⁷`. (For `t < 0`,
`den_rt = ev − tod ≥ ev > 2¹²⁵`, so `DE > S·2¹²⁵ − 2S > 2¹³¹⁷`.) -/
theorem denExpV_lb_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) :
    (2 : Int) ^ 1317 < evalPoly ExpCertV.denExpV (int256 (tTree x)) := by
  obtain ⟨hlo, _⟩ := denExpV_bracket_neg hx hC hC0 htneg
  -- den_rt = ev − tod ≥ ev > 2^125 (tod ≤ 0 on the negative half)
  obtain ⟨hevlo, _⟩ := evTree_facts (vTree_eq hx hC hC0).2
  obtain ⟨htod_lo, htod_hi, _, _⟩ := todTree_bound hx hC hC0
  have hev : (0x4e14a45e8ec305e233e11b4174e214ac : Int) ≤ (evTree x : Int) := by exact_mod_cast hevlo
  rw [show (0x4e14a45e8ec305e233e11b4174e214ac : Int) = 103786963415199049567855548359006885036 from by norm_num] at hev
  -- tod ≤ 0 ⇒ den_rt = ev − tod ≥ ev > 2^125
  have htodnp : int256 (todTree x) ≤ 0 := by
    -- from todTree_bound: 2^128·tod ≤ t·od, t ≤ 0, od ≥ 0 ⇒ t·od ≤ 0 ⇒ tod ≤ 0
    obtain ⟨_, _, htl, _⟩ := todTree_bound hx hC hC0
    have hodnn : (0:Int) ≤ (odTree x : Int) := Int.natCast_nonneg _
    have : int256 (tTree x) * (odTree x : Int) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg htneg hodnn
    nlinarith [htl, this]
  have hden_rt : (2 : Int) ^ 125 < (evTree x : Int) - int256 (todTree x) := by
    rw [show (2:Int)^125 = 42535295865117307932921825928971026432 from by norm_num]
    omega
  have hstep : 2 ^ 1193 * ((evTree x : Int) - int256 (todTree x)) - 2 * 2 ^ 1193 >
      2 ^ 1193 * (2 ^ 125 : Int) - 2 * 2 ^ 1193 := by
    have := mul_lt_mul_of_pos_left hden_rt (by positivity : (0:Int) < 2 ^ 1193)
    linarith [this]
  have hnum : 2 ^ 1193 * (2 ^ 125 : Int) - 2 * 2 ^ 1193 > 2 ^ 1317 := by
    rw [show (2:Int)^1193 * 2 ^ 125 = 2 ^ 1318 from by rw [← pow_add]]
    have h18 : (2:Int)^1318 = 2 * 2 ^ 1317 := by rw [show (1318:Nat) = 1 + 1317 from rfl, pow_add]; ring
    have h93 : (2:Int)^1193 < 2 ^ 1317 := pow_lt_pow_right₀ (by norm_num) (by norm_num)
    nlinarith [h18, h93]
  linarith [hlo, hstep, hnum]

/-- **`r0`-vs-cert-rational bracket (negative half).** Same loose constants as the nonnegative half. -/
theorem r0_vs_certRatio_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) :
    int256 (r0Tree x) * evalPoly ExpCertV.denExpV (int256 (tTree x)) <
        2 ^ 126 * evalPoly ExpCertV.numExpV (int256 (tTree x)) +
          150 * evalPoly ExpCertV.denExpV (int256 (tTree x)) ∧
      2 ^ 126 * evalPoly ExpCertV.numExpV (int256 (tTree x)) <
        (int256 (r0Tree x) + 1) * evalPoly ExpCertV.denExpV (int256 (tTree x)) +
          700 * evalPoly ExpCertV.denExpV (int256 (tTree x)) := by
  obtain ⟨hfloor_lo, hfloor_hi⟩ := r0_floor_sandwich hx hC hC0
  obtain ⟨hnumlo, hnumhi⟩ := numExpV_bracket_neg hx hC hC0 htneg
  obtain ⟨hdenlo, hdenhi⟩ := denExpV_bracket_neg hx hC hC0 htneg
  obtain ⟨hr0lo, hr0hi⟩ := r0Tree_bounds hx hC hC0
  have hdenExpV_lb := denExpV_lb_neg hx hC hC0 htneg
  set r0 := int256 (r0Tree x) with hr0def
  set num := (evTree x : Int) + int256 (todTree x) with hnumdef
  set den := (evTree x : Int) - int256 (todTree x) with hdendef
  set NE := evalPoly ExpCertV.numExpV (int256 (tTree x)) with hNEdef
  set DE := evalPoly ExpCertV.denExpV (int256 (tTree x)) with hDEdef
  have hDEpos : (0 : Int) < DE := by
    have h : (2:Int)^1317 > 0 := by positivity
    linarith [hdenExpV_lb, h]
  have hr0pos : 0 ≤ r0 := by linarith [hr0lo]
  have hr0lt : r0 < 2 ^ 128 := hr0hi
  have hp1193 : (0 : Int) < 2 ^ 1193 := by positivity
  -- DE bounds vs den·2^1193:  DE - 7·2^1193 < den·2^1193 ≤ DE + 2·2^1193
  have hden2_lo : 2 ^ 1193 * den ≤ DE + 2 * 2 ^ 1193 := by linarith [hdenlo]
  have hden2_hi : DE - 7 * 2 ^ 1193 < 2 ^ 1193 * den := by linarith [hdenhi]
  -- NE bounds:  num·2^1193 - 4·2^1193 ≤ NE < num·2^1193 + 5·2^1193
  have hnum2_lo : 2 ^ 1193 * num - 4 * 2 ^ 1193 ≤ NE := by linarith [hnumlo]
  have hnum2_hi : NE < 2 ^ 1193 * num + 5 * 2 ^ 1193 := hnumhi
  -- loss budgets dominated by 150·DE / 700·DE (DE > 2^1317, r0 < 2^128)
  have hr0_loss : 7 * 2 ^ 1193 * r0 + 4 * 2 ^ 126 * 2 ^ 1193 < 150 * DE := by
    have h1 : (7 : Int) * 2 ^ 1193 * r0 < 7 * 2 ^ 1193 * 2 ^ 128 := by
      have := mul_lt_mul_of_pos_left hr0lt (by positivity : (0:Int) < 7 * 2 ^ 1193)
      nlinarith [this]
    have hb : (7 : Int) * 2 ^ 1193 * 2 ^ 128 + 4 * 2 ^ 126 * 2 ^ 1193 < 150 * 2 ^ 1317 := by
      rw [show (7:Int) * 2 ^ 1193 * 2 ^ 128 = 7 * 2 ^ 1321 from by rw [mul_assoc, ← pow_add],
        show (4:Int) * 2 ^ 126 * 2 ^ 1193 = 4 * 2 ^ 1319 from by rw [mul_assoc, ← pow_add],
        show (1321:Nat) = 4 + 1317 from rfl, show (1319:Nat) = 2 + 1317 from rfl, pow_add, pow_add]
      ring_nf; nlinarith [pow_pos (by norm_num : (0:Int)<2) 1317]
    linarith [h1, hb, mul_lt_mul_of_pos_left hdenExpV_lb (by norm_num : (0:Int) < 150)]
  have hunder_loss : 5 * 2 ^ 126 * 2 ^ 1193 + 2 * 2 ^ 1193 * (r0 + 1) < 700 * DE := by
    have h1 : 2 * 2 ^ 1193 * (r0 + 1) < 2 * 2 ^ 1193 * (2 ^ 128 + 1) := by
      apply mul_lt_mul_of_pos_left (by linarith [hr0lt]); positivity
    have hr0p1 : (2 : Int) * 2 ^ 1193 * (2 ^ 128 + 1) < 3 * 2 ^ 1321 := by
      rw [show (1321:Nat) = 4 + 1317 from rfl, pow_add]; ring_nf
      nlinarith [pow_pos (by norm_num : (0:Int)<2) 1193, pow_pos (by norm_num : (0:Int)<2) 1317]
    have h35 : (5 : Int) * 2 ^ 126 * 2 ^ 1193 = 5 * 2 ^ 1319 := by rw [mul_assoc, ← pow_add]
    have hbound : (5 : Int) * 2 ^ 1319 + 3 * 2 ^ 1321 < 700 * 2 ^ 1317 := by
      rw [show (1319:Nat) = 2 + 1317 from rfl, show (1321:Nat) = 4 + 1317 from rfl, pow_add, pow_add]
      ring_nf; nlinarith [pow_pos (by norm_num : (0:Int)<2) 1317]
    rw [h35]
    linarith [h1, hr0p1, hbound, mul_lt_mul_of_pos_left hdenExpV_lb (by norm_num : (0:Int) < 700)]
  have hfl_lo := mul_le_mul_of_nonneg_left hfloor_lo (by positivity : (0:Int) ≤ 2 ^ 1193)
  have hfl_hi := mul_lt_mul_of_pos_left hfloor_hi hp1193
  have hnumstep := mul_le_mul_of_nonneg_left hnum2_lo (by positivity : (0:Int) ≤ 2 ^ 126)
  have hNEstep := mul_lt_mul_of_pos_left hnum2_hi (by positivity : (0:Int) < 2 ^ 126)
  have hr0den_lo := mul_le_mul_of_nonneg_left (le_of_lt hden2_hi) hr0pos
  have hr0den_hi := mul_le_mul_of_nonneg_left hden2_lo (by linarith [hr0pos] : (0:Int) ≤ r0 + 1)
  constructor
  · nlinarith [hfl_lo, hnumstep, hr0den_lo, hr0_loss, hDEpos, hp1193]
  · nlinarith [hfl_hi, hNEstep, hr0den_hi, hunder_loss, hDEpos, hp1193]

/-! ## The octave real identity `E·2^(126−k) = WAD·2¹²⁶·exp(rt)`

The target `E = WAD·exp(X/RAY)`. With `rt = X/RAY − k·ln2` the reduced argument, `exp(X/RAY) =
exp(rt)·2^k`, so the closing-shift fold `E·2^(126−k) = WAD·2¹²⁶·exp(rt)`. This collapses the
`RuntimeR0Bound.over`/`under` inequalities (stated against `E·2^s`, `s = 126 − k`) onto the clean
octave-independent never-over/deficit relation `r0 ≈ 2¹²⁶·exp(rt)`. -/

open ExpRealSpec Real Common.RealExpBridge

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

/-- **The octave fold of the target.** `E·2^(126−k) = WAD·2¹²⁶·exp(rt)`, with `s = 126 − k` the
closing shift. -/
theorem target_octave_fold {x : Nat} (s : Nat) (hs : (s : Int) = 126 - int256 (kTree x)) :
    expRayToWadTarget (int256 x) * (2 ^ s : Real) =
      (WAD : Real) * (2 ^ 126 : Real) * Real.exp (reducedArg x) := by
  unfold expRayToWadTarget
  rw [show (RAY : Real) = (10 ^ 27 : Real) from by unfold RAY; norm_num, exp_X_over_RAY x]
  -- 2^k · 2^s = 2^126 with k+s = 126 (k : Int, s : Nat).
  set k := int256 (kTree x) with hkdef
  have hks : k + (s : Int) = 126 := by omega
  have hpow : (2 : Real) ^ k * (2 : Real) ^ (s : Nat) = (2 : Real) ^ (126 : Nat) := by
    rw [show ((2 : Real) ^ (s : Nat)) = (2 : Real) ^ (s : Int) from by
      rw [zpow_natCast], ← zpow_add₀ (by norm_num : (2:Real) ≠ 0), hks]
    norm_num
  rw [show ((2 ^ s : Real)) = (2 : Real) ^ (s : Nat) from by norm_num]
  calc (WAD : Real) * (Real.exp (reducedArg x) * (2 : Real) ^ k) * (2 : Real) ^ (s : Nat)
      = (WAD : Real) * ((2 : Real) ^ k * (2 : Real) ^ (s : Nat)) * Real.exp (reducedArg x) := by ring
    _ = (WAD : Real) * (2 ^ 126 : Real) * Real.exp (reducedArg x) := by
          rw [hpow]

/-! ## The cert `Real.exp` bounds at the runtime reduced argument (nonnegative half)

Instantiating the v-form Taylor caps (`ExpCertV.capExpUp`/`capExpLo`) at `t = int256 (tTree x)` (in
the cert domain `[0, H128]` on the nonnegative half) and pushing through the abstract
`Common.RealExpBridge` yields `Real.exp(t/2¹²⁸)` bracketed by the margin-nudged rational `ê_v =
NE/DE`. Both `NE = evalPoly numExpV t` and `DE = evalPoly denExpV t` are positive on the domain. -/

/-- The numerator/denominator cert-polynomial values are nonnegative / positive on `[0, H128]`. -/
theorem certNE_nonneg {t : Int} (h1 : 0 ≤ t) (h2 : t ≤ (ExpCertV.H128 : Int)) :
    0 ≤ evalPoly ExpCertV.numExpV t := ExpCertV.numExpV_nonneg' h1 h2

theorem certDE_pos {t : Int} (h1 : 0 ≤ t) (h2 : t ≤ (ExpCertV.H128 : Int)) :
    1 ≤ evalPoly ExpCertV.denExpV t := ExpCertV.denExpV_ge_one h1 h2

/-- **Never-over cert real bound (nonneg half).** `(2¹³⁰−1)·NE / (2¹³⁰·DE) ≤ exp(t/2¹²⁸)`, the
not-two-below cap pushed to `Real.exp`. -/
theorem certLo_real {t : Int} (h1 : 0 ≤ t) (h2 : t ≤ (ExpCertV.H128 : Int)) :
    ((2 ^ 130 - 1 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real) /
        (((2 ^ 130 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real)) ≤
      Real.exp ((t : Real) / (2 ^ 128 : Real)) := by
  have hcap := ExpCertV.capExpLo h1 h2
  have hwpos : 0 < (evalPoly ExpCertV.wLB t).toNat := by
    have hpos : 0 < evalPoly ExpCertV.wLB t := by
      rw [ExpCertV.evalWLB]
      exact mul_pos (by norm_num) (by have := certDE_pos h1 h2; omega)
    omega
  have h := le_exp_of_capLB (q := ExpCertV.Qexp) ExpCertV.Qexp_pos hwpos hcap
  -- the cap is on `(t.toNat : Real)/Qexp`; rewrite to `(t:Real)/2^128`
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
  -- rewrite yLB/wLB to (2^130-1)·NE / (2^130·DE)
  have hynr : ((evalPoly ExpCertV.yLB t).toNat : Real) = ((2 ^ 130 - 1 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real) := by
    have : ((evalPoly ExpCertV.yLB t).toNat : Int) = (2 ^ 130 - 1) * evalPoly ExpCertV.numExpV t := by
      rw [hyn, ExpCertV.evalYLB]
    have := congrArg (fun z : Int => (z : Real)) this
    push_cast at this ⊢; linarith [this]
  have hwnr : ((evalPoly ExpCertV.wLB t).toNat : Real) = ((2 ^ 130 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real) := by
    have : ((evalPoly ExpCertV.wLB t).toNat : Int) = 2 ^ 130 * evalPoly ExpCertV.denExpV t := by
      rw [hwn, ExpCertV.evalWLB]
    have := congrArg (fun z : Int => (z : Real)) this
    push_cast at this ⊢; linarith [this]
  rw [hynr, hwnr] at h
  exact h

/-- **Not-two-below cert real bound (nonneg half).** `exp(t/2¹²⁸) ≤ (2¹³⁰+1)·NE / (2¹³⁰·DE)`. -/
theorem certUp_real {t : Int} (h1 : 0 ≤ t) (h2 : t ≤ (ExpCertV.H128 : Int)) :
    Real.exp ((t : Real) / (2 ^ 128 : Real)) ≤
      ((2 ^ 130 + 1 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real) /
        (((2 ^ 130 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real)) := by
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
  have hynr : ((evalPoly ExpCertV.yUB t).toNat : Real) = ((2 ^ 130 + 1 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real) := by
    have : ((evalPoly ExpCertV.yUB t).toNat : Int) = (2 ^ 130 + 1) * evalPoly ExpCertV.numExpV t := by
      rw [hyn, ExpCertV.evalYUB]
    have := congrArg (fun z : Int => (z : Real)) this
    push_cast at this ⊢; linarith [this]
  have hwnr : ((evalPoly ExpCertV.wUB t).toNat : Real) = ((2 ^ 130 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real) := by
    have : ((evalPoly ExpCertV.wUB t).toNat : Int) = 2 ^ 130 * evalPoly ExpCertV.denExpV t := by
      rw [hwn, ExpCertV.evalWUB]
    have := congrArg (fun z : Int => (z : Real)) this
    push_cast at this ⊢; linarith [this]
  rw [hynr, hwnr] at h
  exact h

/-! ## The cert `Real.exp` bounds at a negative reduced argument (via the reciprocal symmetry)

For `t ≤ 0` (with `−t ∈ [0, H128]`) the cert at `u = −t`, composed with `numExpV(−t) = denExpV(t)`,
`denExpV(−t) = numExpV(t)` and `exp(−s) = 1/exp(s)`, brackets `exp(t/2¹²⁸)` against the same
margin-nudged rational `NE(t)/DE(t)` — the over side needs `NE/DE ≤ exp·(2¹³⁰+1)/2¹³⁰`, the under
side `exp ≤ (NE/DE)·2¹³⁰/(2¹³⁰−1)`. The cert denominators `NE(t)`, `DE(t)` are positive. -/

/-- For `t ≤ 0` with `−t ∈ [0, H128]` the cert numerator/denominator at `t` are positive. -/
theorem certNE_pos_neg_aux {t : Int} (h1 : t ≤ 0) (h2 : (-t) ≤ (ExpCertV.H128 : Int)) :
    0 < evalPoly ExpCertV.numExpV t ∧ 0 < evalPoly ExpCertV.denExpV t := by
  have hnt : 0 ≤ -t := by omega
  -- numExpV(t) = denExpV(-t) ≥ 1 > 0
  have h1' : evalPoly ExpCertV.numExpV t = evalPoly ExpCertV.denExpV (-t) := by
    have := numExpV_neg_eq_denExpV (-t); rwa [neg_neg] at this
  have hde : 1 ≤ evalPoly ExpCertV.denExpV (-t) := ExpCertV.denExpV_ge_one hnt h2
  -- denExpV(t) = evNumVPoly(t) − todNumV(t); for t ≤ 0, todNumV(t) ≤ 0, and evNumVPoly(t) ≥ 1
  have htod_np : evalPoly ExpCertV.todNumV t ≤ 0 := by
    rw [evalTodNumV]
    have hodnn := odNumVPoly_nonneg t
    have : t * evalPoly ExpCertV.odNumVPoly t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 hodnn
    nlinarith [this]
  have hev1 : 1 ≤ evalPoly ExpCertV.evNumVPoly t := by
    -- evNumVPoly(t) = evNumVPoly(-t) (even) ≥ denExpV(-t) ≥ 1 (todNumV(-t) ≥ 0)
    have heven : evalPoly ExpCertV.evNumVPoly t = evalPoly ExpCertV.evNumVPoly (-t) := by
      rw [← evNumVPoly_even (-t), neg_neg]
    have htodnt : 0 ≤ evalPoly ExpCertV.todNumV (-t) := by
      rw [evalTodNumV]
      exact Int.mul_nonneg (by positivity) (Int.mul_nonneg hnt (odNumVPoly_nonneg (-t)))
    have hde' := hde
    rw [evalDenExpV] at hde'
    rw [heven]; linarith [hde', htodnt]
  refine ⟨by rw [h1']; omega, ?_⟩
  rw [evalDenExpV]; linarith [hev1, htod_np]

/-- **Never-too-below cert real bound (negative half).** For `t ≤ 0` with `−t ∈ [0, H128]`:
`exp(t/2¹²⁸) ≤ (2¹³⁰·NE) / ((2¹³⁰−1)·DE)`. -/
theorem certUp_real_neg {t : Int} (h1 : t ≤ 0) (h2 : (-t) ≤ (ExpCertV.H128 : Int)) :
    Real.exp ((t : Real) / (2 ^ 128 : Real)) ≤
      ((2 ^ 130 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real) /
        (((2 ^ 130 - 1 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real)) := by
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
  have hlhs_pos : (0:Real) < ((2 ^ 130 - 1 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real) /
      (((2 ^ 130 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real)) := by positivity
  rw [le_inv_comm₀ hlhs_pos hexppos] at hcl
  calc Real.exp ((t : Real) / (2 ^ 128 : Real))
      ≤ (((2 ^ 130 - 1 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real) /
          (((2 ^ 130 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real)))⁻¹ := hcl
    _ = ((2 ^ 130 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real) /
          (((2 ^ 130 - 1 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real)) := by
        rw [inv_div]

/-- **Never-over cert real bound (negative half).** For `t ≤ 0` with `−t ∈ [0, H128]`:
`(2¹³⁰·NE) / ((2¹³⁰+1)·DE) ≤ exp(t/2¹²⁸)`. -/
theorem certLo_real_neg {t : Int} (h1 : t ≤ 0) (h2 : (-t) ≤ (ExpCertV.H128 : Int)) :
    ((2 ^ 130 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real) /
        (((2 ^ 130 + 1 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real)) ≤
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
  have hrhs_pos : (0:Real) < ((2 ^ 130 + 1 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real) /
      (((2 ^ 130 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real)) := by positivity
  rw [inv_le_comm₀ hexppos hrhs_pos] at hcu
  calc ((2 ^ 130 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real) /
        (((2 ^ 130 + 1 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real))
      = (((2 ^ 130 + 1 : Int) : Real) * (evalPoly ExpCertV.denExpV t : Real) /
          (((2 ^ 130 : Int) : Real) * (evalPoly ExpCertV.numExpV t : Real)))⁻¹ := by
        rw [inv_div]
    _ ≤ Real.exp ((t : Real) / (2 ^ 128 : Real)) := hcu

/-- On the nonnegative half of the region the reduced argument is below `ln2/2`:
`t/2¹²⁸ ≤ log 2 / 2`. -/
theorem t_over_2128_le_half_log2 {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    (int256 (tTree x) : Real) / (2 ^ 128 : Real) ≤ Real.log 2 / 2 := by
  obtain ⟨_, hthi⟩ := tTree_in_cert_domain hx hC hC0
  -- t ≤ H128 ≤ ⌊ln2/2·2^128⌋, and LN2/2^235 ≤ ln2 gives H128/2^128 ≤ ln2/2
  have hln2lo := ln2_lower
  rw [LN2c_eq] at hln2lo
  -- LN2/2^235 ≤ log 2. H128 = 117932881612756647068972071382077242199.
  -- t/2^128 ≤ H128/2^128. need H128/2^128 ≤ log2/2. Use 2·H128/2^128 ≤ 2·(ln2/2) = ln2.
  have htR : (int256 (tTree x) : Real) ≤ (117932881612756647068972071382077242199 : Real) := by
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hthi; push_cast at this; linarith [this]
  have hp128 : (0 : Real) < (2 ^ 128 : Real) := by positivity
  rw [div_le_div_iff₀ hp128 (by norm_num : (0:Real) < 2)]
  -- t·2 ≤ log2·2^128. Have t ≤ H128, and 2·H128 ≤ log2·2^128 (from LN2 bound).
  have hkey : (2 : Real) * (117932881612756647068972071382077242199 : Real) ≤ Real.log 2 * (2 ^ 128 : Real) := by
    -- log2 ≥ LN2/2^235 ⟹ log2·2^128 ≥ LN2·2^128/2^235 = LN2/2^107. Check 2·H128 ≤ LN2/2^107.
    have h1 : (38271408169742254668347313025622401492114385419650052359639581444463709 : Real) / (2 ^ 235 : Real) * (2 ^ 128 : Real) ≤ Real.log 2 * (2 ^ 128 : Real) := by
      apply mul_le_mul_of_nonneg_right hln2lo (by positivity)
    have h2 : (2 : Real) * (117932881612756647068972071382077242199 : Real) ≤
        (38271408169742254668347313025622401492114385419650052359639581444463709 : Real) / (2 ^ 235 : Real) * (2 ^ 128 : Real) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:Real) < 2 ^ 235)]
      norm_num
    linarith [h1, h2]
  nlinarith [htR, hkey]

/-- The reduced exponential is below `√2 < 2` (loose). -/
theorem exp_reducedArg_le_two {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    Real.exp (reducedArg x) ≤ 2 := by
  -- |rt| ≤ ln2/2 + tiny ⟹ rt < log2 ⟹ exp(rt) < exp(log2) = 2; we prove ≤ 2 generously.
  obtain ⟨htlo, hthi⟩ := tTree_in_cert_domain hx hC hC0
  have hclose := reducedArg_close hx hC hC0
  have habs := abs_lt.mp hclose
  -- rt < t/2^128 + 9/(8·2^128) ≤ H128/2^128 + 1 < log2 (very loose: H128/2^128 < 0.347)
  have hp128 : (0 : Real) < (2 ^ 128 : Real) := by positivity
  have htR : (int256 (tTree x) : Real) ≤ (117932881612756647068972071382077242199 : Real) := by
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hthi; push_cast at this; linarith [this]
  have hln2 : (0.6931471805 : Real) ≤ Real.log 2 := by
    have := ln2_lower; rw [LN2c_eq] at this
    have h2 : (0.6931471805 : Real) ≤ (38271408169742254668347313025622401492114385419650052359639581444463709 : Real) / (2 ^ 235 : Real) := by
      rw [le_div_iff₀ (by positivity : (0:Real) < 2 ^ 235)]; norm_num
    linarith [this, h2]
  have hrtlt : reducedArg x ≤ Real.log 2 := by
    have h9 : (9 : Real) / (8 * (2 ^ 128 : Real)) ≤ 1 := by
      rw [div_le_one (by positivity)]; norm_num
    have htdiv : (int256 (tTree x) : Real) / (2 ^ 128 : Real) ≤ 0.35 := by
      rw [div_le_iff₀ hp128]; nlinarith [htR]
    -- rt < t/2^128 + 9/(8·2^128) ≤ 0.35 + 1 ... too loose vs log2 ≈ 0.693. tighten 9/8 bound.
    have h9' : (9 : Real) / (8 * (2 ^ 128 : Real)) ≤ 0.34 := by
      rw [div_le_iff₀ (by positivity)]; norm_num
    linarith [habs.2, htdiv, h9', hln2]
  calc Real.exp (reducedArg x) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hrtlt
    _ = 2 := Real.exp_log (by norm_num)

/-- `exp(t/2¹²⁸) ≤ 2` (loose). -/
theorem exp_t_le_two {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    Real.exp ((int256 (tTree x) : Real) / (2 ^ 128 : Real)) ≤ 2 := by
  have hle := t_over_2128_le_half_log2 hx hC hC0 htnn
  have hhalf : Real.log 2 / 2 ≤ Real.log 2 := by
    have : (0:Real) ≤ Real.log 2 := by rw [Real.le_log_iff_exp_le (by norm_num)]; simp [Real.exp_zero]
    linarith
  calc Real.exp ((int256 (tTree x) : Real) / (2 ^ 128 : Real))
      ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (le_trans hle hhalf)
    _ = 2 := Real.exp_log (by norm_num)

/-- The convexity bound `exp(b) − exp(a) ≤ (b−a)·exp(b)`. -/
theorem exp_diff_le (a b : Real) : Real.exp b - Real.exp a ≤ (b - a) * Real.exp b := by
  have key : Real.exp a = Real.exp (a - b) * Real.exp b := by rw [← Real.exp_add]; ring_nf
  have h1 : a - b + 1 ≤ Real.exp (a - b) := Real.add_one_le_exp (a - b)
  have hb : 0 < Real.exp b := Real.exp_pos b
  rw [key]; nlinarith [h1, hb]

/-! ## The tight joint per-point never-over (nonnegative half) -/

-- exp(t/2^128) ≤ √2 on the nonneg half.
theorem exp_t_le_sqrt2 {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    Real.exp ((int256 (tTree x) : Real) / (2 ^ 128 : Real)) ≤ Real.sqrt 2 := by
  have hle := t_over_2128_le_half_log2 hx hC hC0 htnn
  calc Real.exp ((int256 (tTree x) : Real) / (2 ^ 128 : Real))
      ≤ Real.exp (Real.log 2 / 2) := Real.exp_le_exp.mpr hle
    _ = Real.sqrt 2 := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0:Real) < 2)]; ring_nf

-- den ≥ A4 − 2^125 (≈ 0.72·2^126): den = ev − tod, ev ≥ A4, tod < 2^125.
theorem den_ge_072 {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (61251667550081741634933722430035858604 : Int) ≤
      (evTree x : Int) - int256 (todTree x) := by
  obtain ⟨hevlo, _⟩ := evTree_facts (vTree_eq hx hC hC0).2
  obtain ⟨_, htod_hi, _, _⟩ := todTree_bound hx hC hC0
  have hev : (103786963415199049567855548359006885036 : Int) ≤ (evTree x : Int) := by exact_mod_cast hevlo
  have ht125 : int256 (todTree x) < 2 ^ 125 := by
    rw [show (2:Int)^125 = 42535295865117307932921825928971026432 from by norm_num]; exact htod_hi
  rw [show (2:Int)^125 = 42535295865117307932921825928971026432 from by norm_num] at ht125
  omega

/-- **The joint per-point never-over (nonneg half).** `r0 ≤ 2¹²⁶·exp(rt) + 19/25` — within the
`MARGIN/WAD = 0.792` budget. Combines the joint cert-ratio over (the shared even truncation cancels
via the floor), `exp(t/2¹²⁸) ≤ √2`, `den ≥ 0.72·2¹²⁶`, and the tight one-sided gap-1. -/
theorem r0_real_over_tight {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    (int256 (r0Tree x) : Real) ≤ (2 ^ 126 : Real) * Real.exp (reducedArg x) + 19 / 25 := by
  obtain ⟨_, hthi⟩ := tTree_in_cert_domain hx hC hC0
  set t := int256 (tTree x) with htdef
  have htdom : t ≤ (ExpCertV.H128 : Int) := by
    rw [show ((ExpCertV.H128 : Nat) : Int) = 117932881612756647068972071382077242199 from by
      unfold ExpCertV.H128; norm_num]
    exact hthi
  have hDElb := denExpV_lb hx hC hC0 htnn
  set NE := evalPoly ExpCertV.numExpV t with hNEdef
  set DE := evalPoly ExpCertV.denExpV t with hDEdef
  have hDEpos_int : (0 : Int) < DE := by
    have : (0:Int) < 2 ^ 1317 := by positivity
    linarith [hDElb, this]
  have hDEpos : (0 : Real) < (DE : Real) := by exact_mod_cast hDEpos_int
  have hNEnn : (0 : Real) ≤ (NE : Real) := by
    have := certNE_nonneg htnn htdom; exact_mod_cast this
  set r0 := int256 (r0Tree x) with hr0def
  -- certLo: NE/DE ≤ Et·Mp, Mp = 2^130/(2^130−1); Et = exp(t/2^128) ≤ √2.
  set Et := Real.exp ((t : Real) / (2 ^ 128 : Real)) with hEtdef
  have hcertlo := certLo_real htnn htdom
  set Mp : Real := (2 ^ 130 : Real) / ((2 ^ 130 : Real) - 1) with hMpdef
  have hEtsqrt2 := exp_t_le_sqrt2 hx hC hC0 htnn
  rw [← hEtdef] at hEtsqrt2
  have hEtnn : (0 : Real) ≤ Et := le_of_lt (Real.exp_pos _)
  have hNEDE_le : (NE : Real) / (DE : Real) ≤ Et * Mp := by
    have hc : ((2 ^ 130 - 1 : Int) : Real) * (NE : Real) /
        (((2 ^ 130 : Int) : Real) * (DE : Real)) ≤ Et := hcertlo
    rw [hMpdef]
    have key : (NE : Real) / (DE : Real) =
        ((2 ^ 130 : Real) / ((2 ^ 130 : Real) - 1)) *
          (((2 ^ 130 - 1 : Int) : Real) * (NE : Real) /
            (((2 ^ 130 : Int) : Real) * (DE : Real))) := by
      push_cast; field_simp; ring
    rw [key, mul_comm Et _]; exact mul_le_mul_of_nonneg_left hc (by positivity)
  -- r0 ≤ 2^126·num/den (floor)
  obtain ⟨hfloor_lo, _⟩ := r0_floor_sandwich hx hC hC0
  obtain ⟨hnumlo, _⟩ := numExpV_bracket hx hC hC0 htnn
  obtain ⟨_, hdenhi⟩ := denExpV_bracket hx hC hC0 htnn
  set num := (evTree x : Int) + int256 (todTree x) with hnumdef
  set den := (evTree x : Int) - int256 (todTree x) with hdendef
  have hden072 : (61251667550081741634933722430035858604 : Int) ≤ den := den_ge_072 hx hC hC0
  have hdenpos : (0:Int) < den := lt_of_lt_of_le (by norm_num) hden072
  have hdenR : (0:Real) < (den : Real) := by exact_mod_cast hdenpos
  have hden072R : (61251667550081741634933722430035858604 : Real) ≤ (den : Real) := by
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hden072; push_cast at this; linarith [this]
  have hr0_le_numden : (r0 : Real) ≤ (2 ^ 126 : Real) * (num : Real) / (den : Real) := by
    rw [le_div_iff₀ hdenR]
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hfloor_lo; push_cast at this; nlinarith [this]
  -- bound num: 2^1193·num ≤ NE ≤ Et·Mp·DE ≤ √2·Mp·DE; DE < 2^1193·den + 3·2^1193 (denExpV hi)
  have hnumloR : (2 ^ 1193 : Real) * (num : Real) ≤ (NE : Real) := by
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hnumlo; push_cast at this; linarith [this]
  have hdenhiR : (DE : Real) < (2 ^ 1193 : Real) * (den : Real) + 3 * 2 ^ 1193 := by
    have := (@Int.cast_lt Real _ _ _ _ _ _ _).mpr hdenhi; push_cast at this; linarith [this]
  have hMp_pos : (0:Real) < Mp := by rw [hMpdef]; positivity
  -- NE ≤ √2·Mp·DE
  have hNE_le : (NE : Real) ≤ Real.sqrt 2 * Mp * (DE : Real) := by
    have h1 : (NE : Real) ≤ Et * Mp * (DE : Real) := by
      have := mul_le_mul_of_nonneg_right hNEDE_le (le_of_lt hDEpos)
      rwa [div_mul_cancel₀ _ (ne_of_gt hDEpos)] at this
    have h2 : Et * Mp * (DE : Real) ≤ Real.sqrt 2 * Mp * (DE : Real) := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hDEpos)
      exact mul_le_mul_of_nonneg_right hEtsqrt2 (le_of_lt hMp_pos)
    linarith [h1, h2]
  -- num ≤ √2·Mp·(den + 3)
  have hnum_le : (num : Real) ≤ Real.sqrt 2 * Mp * ((den : Real) + 3) := by
    have hp : (0:Real) < (2 ^ 1193 : Real) := by positivity
    rw [← mul_le_mul_left hp]
    calc (2 ^ 1193 : Real) * (num : Real) ≤ (NE : Real) := hnumloR
      _ ≤ Real.sqrt 2 * Mp * (DE : Real) := hNE_le
      _ ≤ Real.sqrt 2 * Mp * ((2 ^ 1193 : Real) * (den : Real) + 3 * 2 ^ 1193) := by
          apply mul_le_mul_of_nonneg_left (le_of_lt hdenhiR)
          rw [hMpdef]; positivity
      _ = (2 ^ 1193 : Real) * (Real.sqrt 2 * Mp * ((den : Real) + 3)) := by ring
  -- √2 ≤ 14143/10000 (since (14143/10000)² > 2)
  have hsqrt2_val : Real.sqrt 2 ≤ 14143 / 10000 := by
    rw [Real.sqrt_le_iff]; constructor <;> norm_num
  have hsqrt2_nn : (0:Real) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  -- Mp ≤ 14143/10000 ⁻¹ ... we need √2·Mp ≤ 14144/10000 (a hair above √2; Mp = 1 + 1/(2^130−1))
  have hMp_le : Mp ≤ 14144 / 14143 := by
    rw [hMpdef, div_le_div_iff₀ (by norm_num) (by norm_num)]
    have h130 : (14144 : Real) ≤ 2 ^ 130 := by
      rw [show (2:Real) ^ 130 = 1361129467683753853853498429727072845824 from by norm_num]; norm_num
    nlinarith [h130]
  -- √2·Mp ≤ 14144/10000
  have hsM_le : Real.sqrt 2 * Mp ≤ 14144 / 10000 := by
    have hMpnn : (0:Real) ≤ Mp := by rw [hMpdef]; positivity
    calc Real.sqrt 2 * Mp ≤ (14143 / 10000) * (14144 / 14143) :=
          mul_le_mul hsqrt2_val hMp_le hMpnn (by norm_num)
      _ = 14144 / 10000 := by norm_num
  -- (r0 − 2^126)·den ≤ 2^126·(num − den) ≤ 2^126·(√2·Mp·(den+3) − den) ≤ 2^126·(4145/10000)·den
  have hr0_den : ((r0 : Real) - 2 ^ 126) * (den : Real) ≤ (2 ^ 126 : Real) * (4145 / 10000) * (den : Real) := by
    -- floor (Real): r0·den ≤ 2^126·num
    have hfl : (r0 : Real) * (den : Real) ≤ (2 ^ 126 : Real) * (num : Real) := by
      have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hfloor_lo; push_cast at this; linarith [this]
    -- num ≤ √2·Mp·(den+3) ≤ (14144/10000)·(den+3)
    have hnum2 : (num : Real) ≤ (14144 / 10000) * ((den : Real) + 3) := by
      have hpos : (0:Real) ≤ (den : Real) + 3 := by linarith [hden072R]
      calc (num : Real) ≤ Real.sqrt 2 * Mp * ((den : Real) + 3) := hnum_le
        _ ≤ (14144 / 10000) * ((den : Real) + 3) := mul_le_mul_of_nonneg_right hsM_le hpos
    -- (r0−2^126)·den = r0·den − 2^126·den ≤ 2^126·num − 2^126·den
    have hstep1 : ((r0 : Real) - 2 ^ 126) * (den : Real) ≤ (2 ^ 126 : Real) * (num : Real) - 2 ^ 126 * (den : Real) := by
      nlinarith [hfl]
    -- 2^126·num ≤ 2^126·(14144/10000)·(den+3)  (scale hnum2 by 2^126 > 0)
    have hstep2 : (2 ^ 126 : Real) * (num : Real) ≤ (2 ^ 126 : Real) * ((14144 / 10000) * ((den : Real) + 3)) :=
      mul_le_mul_of_nonneg_left hnum2 (by positivity)
    -- 2^126·(14144/10000·(den+3)) − 2^126·den ≤ 2^126·(4145/10000)·den  ⟺  42432 ≤ den (from den ≥ 0.72·2^126)
    have hden42432 : (42432 : Real) ≤ (den : Real) := by
      have h : (42432 : Real) ≤ 61251667550081741634933722430035858604 := by norm_num
      linarith [hden072R, h]
    nlinarith [hstep1, hstep2, hden42432, mul_pos (by norm_num : (0:Real) < 2^126) hdenR]
  have hr0m_bound : (r0 : Real) - 2 ^ 126 ≤ (2 ^ 126 : Real) * 4145 / 10000 := by
    have hkey : ((r0 : Real) - 2 ^ 126) * (den : Real) ≤ ((2 ^ 126 : Real) * 4145 / 10000) * (den : Real) := by
      have : (2 ^ 126 : Real) * (4145 / 10000) * (den : Real) = ((2 ^ 126 : Real) * 4145 / 10000) * (den : Real) := by ring
      linarith [hr0_den, this ▸ hr0_den]
    exact le_of_mul_le_mul_right hkey hdenR
  -- DE ≥ 2^1193·den − 32·2^1193  (denExpV lo bracket)
  obtain ⟨hdenlo, _⟩ := denExpV_bracket hx hC hC0 htnn
  have hDElo32 : (2 ^ 1193 : Real) * (den : Real) - 32 * 2 ^ 1193 ≤ (DE : Real) := by
    have h := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hdenlo
    push_cast at h
    rw [hdendef, hDEdef]; push_cast; linarith [h]
  -- cR term: W_ev·(r0−2^126)/DE ≤ 64/100  (provable ≈ 0.62)
  have hr0m_nn : (0:Real) ≤ (r0 : Real) - 2 ^ 126 ∨ (r0 : Real) - 2 ^ 126 < 0 := le_or_gt _ _ |>.imp_left id
  have hcR : (1130577 : Real) * 2 ^ 1173 * ((r0 : Real) - 2 ^ 126) / (DE : Real) ≤ 64 / 100 := by
    rcases le_or_gt ((r0:Real) - 2^126) 0 with hle0 | hgt0
    · -- numerator ≤ 0, so the fraction ≤ 0 ≤ 64/100
      have hnumneg : (1130577 : Real) * 2 ^ 1173 * ((r0 : Real) - 2 ^ 126) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hle0
      have : (1130577 : Real) * 2 ^ 1173 * ((r0 : Real) - 2 ^ 126) / (DE : Real) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hnumneg (le_of_lt hDEpos)
      linarith [this]
    · -- 0 < r0−2^126 ≤ 2^126·4145/10000; DE ≥ 2^1193(den−32) > 0 with den ≥ 0.72·2^126
      rw [div_le_iff₀ hDEpos]
      -- W_ev·(r0−2^126) ≤ (64/100)·DE.  W_ev = 1130577·2^1173.  use DE ≥ 2^1193(den−32).
      have hnum_le : (1130577 : Real) * 2 ^ 1173 * ((r0 : Real) - 2 ^ 126) ≤
          1130577 * 2 ^ 1173 * ((2 ^ 126 : Real) * 4145 / 10000) :=
        mul_le_mul_of_nonneg_left hr0m_bound (by positivity)
      -- (64/100)·DE ≥ (64/100)·2^1193·(den−32); need W_ev·2^126·4145/10000 ≤ (64/100)·2^1193·(den−32)
      have hbudget : (1130577 : Real) * 2 ^ 1173 * ((2 ^ 126 : Real) * 4145 / 10000) ≤
          (64 / 100) * ((2 ^ 1193 : Real) * (den : Real) - 32 * 2 ^ 1193) := by
        -- both sides are (·)·2^1193.  LHS = (1130577·4145/10000·2^106)·2^1193; RHS = (64/100·(den−32))·2^1193
        have hLHS : (1130577 : Real) * 2 ^ 1173 * ((2 ^ 126 : Real) * 4145 / 10000) =
            (1130577 * 4145 / 10000 * 2 ^ 106) * 2 ^ 1193 := by
          have e1 : (2:Real) ^ 1173 * 2 ^ 126 = 2 ^ 106 * 2 ^ 1193 := by
            rw [← pow_add, ← pow_add]
          linear_combination (1130577 * 4145 / 10000) * e1
        have hRHS : (64 / 100 : Real) * ((2 ^ 1193 : Real) * (den : Real) - 32 * 2 ^ 1193) =
            (64 / 100 * ((den : Real) - 32)) * 2 ^ 1193 := by ring
        rw [hLHS, hRHS]
        have hp : (0:Real) < (2 ^ 1193 : Real) := by positivity
        rw [mul_le_mul_right hp]
        have h106 : (1130577 * 4145 / 10000 * 2 ^ 106 : Real) ≤
            64 / 100 * (61251667550081741634933722430035858604 - 32) := by
          rw [show (2:Real) ^ 106 = 81129638414606681695789005144064 from by norm_num]; norm_num
        nlinarith [h106, hden072R]
      calc (1130577 : Real) * 2 ^ 1173 * ((r0 : Real) - 2 ^ 126)
          ≤ 1130577 * 2 ^ 1173 * ((2 ^ 126 : Real) * 4145 / 10000) := hnum_le
        _ ≤ (64 / 100) * ((2 ^ 1193 : Real) * (den : Real) - 32 * 2 ^ 1193) := hbudget
        _ ≤ (64 / 100) * (DE : Real) := mul_le_mul_of_nonneg_left hDElo32 (by norm_num)
  -- r0 ≤ 2^126·NE/DE + 64/100 (case-split: small ⟹ r0·DE ≤ 2^126·NE; big ⟹ joint + hcR)
  have hr0_div : (r0 : Real) ≤ (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) + 64 / 100 := by
    rcases le_or_gt r0 (2^126) with hsm | hbg
    · -- small: r0·DE ≤ 2^126·NE (r0_certRatio_over_small), so r0 ≤ 2^126·NE/DE ≤ … + 64/100
      have hi := r0_certRatio_over_small hx hC hC0 htnn hsm
      have hiR : (r0 : Real) * (DE : Real) ≤ (2 ^ 126 : Real) * (NE : Real) := by
        have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hi; push_cast at this; linarith [this]
      have hr0le : (r0 : Real) ≤ (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) := by
        rw [mul_div_assoc', le_div_iff₀ hDEpos]; linarith [hiR]
      linarith [hr0le]
    · -- big: r0·DE − 2^126·NE ≤ W_ev·(r0−2^126) (joint tight); divide by DE; add hcR
      have hi := r0_certRatio_over_tight hx hC hC0 htnn (le_of_lt hbg)
      have hjointR : (r0 : Real) * (DE : Real) - (2 ^ 126 : Real) * (NE : Real) ≤
          (1130577 : Real) * 2 ^ 1173 * ((r0 : Real) - 2 ^ 126) := by
        have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hi; push_cast at this; linarith [this]
      have hstep : (r0 : Real) ≤ (2 ^ 126 : Real) * (NE : Real) / (DE : Real) +
          (1130577 : Real) * 2 ^ 1173 * ((r0 : Real) - 2 ^ 126) / (DE : Real) := by
        rw [div_add_div_same, le_div_iff₀ hDEpos]; nlinarith [hjointR, hDEpos]
      rw [mul_div_assoc] at hstep
      linarith [hstep, hcR]
  -- 2^126·NE/DE ≤ 2^126·Et·Mp = 2^126·Et + 2^126·Et·(Mp−1); cMp = 2^126·Et·(Mp−1) ≤ small
  have hMp1 : Mp - 1 = 1 / (2 ^ 130 - 1 : Real) := by rw [hMpdef]; field_simp
  have hcMp : (2 ^ 126 : Real) * Et * (Mp - 1) ≤ 1 / 10 := by
    rw [hMp1]
    have hb : (2 ^ 126 : Real) * Et * (1 / (2 ^ 130 - 1 : Real)) ≤
        (2 ^ 126 : Real) * Real.sqrt 2 * (1 / (2 ^ 130 - 1 : Real)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hEtsqrt2 (by positivity)
    have hn : (2 ^ 126 : Real) * Real.sqrt 2 * (1 / (2 ^ 130 - 1 : Real)) ≤ 1 / 10 := by
      rw [mul_one_div, div_le_div_iff₀ (by norm_num) (by norm_num)]
      nlinarith [hsqrt2_val, hsqrt2_nn]
    linarith [hb, hn]
  -- gap1: Et − exp(rt) ≤ (t/2^128 − rt)·Et < (1/(32·2^128))·Et ≤ (1/(32·2^128))·√2
  set Ert := Real.exp (reducedArg x) with hErtdef
  have hgapover := reducedArg_close_over hx hC hC0
  have hExp_diff : Et - Ert ≤ ((t : Real) / (2 ^ 128 : Real) - reducedArg x) * Et := exp_diff_le _ _
  have hcGap1 : (2 ^ 126 : Real) * (Et - Ert) ≤ 1 / 50 := by
    have h1 : Et - Ert ≤ (1 / (32 * (2 ^ 128 : Real))) * Et :=
      le_trans hExp_diff (mul_le_mul_of_nonneg_right (le_of_lt hgapover) hEtnn)
    have h2 : (2 ^ 126 : Real) * (Et - Ert) ≤ (2 ^ 126 : Real) * ((1 / (32 * (2 ^ 128 : Real))) * Et) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (2 ^ 126 : Real) * ((1 / (32 * (2 ^ 128 : Real))) * Et) ≤
        (2 ^ 126 : Real) * ((1 / (32 * (2 ^ 128 : Real))) * Real.sqrt 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEtsqrt2 (by positivity)) (by positivity)
    have h4 : (2 ^ 126 : Real) * ((1 / (32 * (2 ^ 128 : Real))) * Real.sqrt 2) ≤ 1 / 50 := by
      rw [show (2 ^ 126 : Real) * ((1 / (32 * (2 ^ 128 : Real))) * Real.sqrt 2) =
            Real.sqrt 2 * (2 ^ 126 / (32 * 2 ^ 128)) from by ring]
      have : (2 ^ 126 : Real) / (32 * 2 ^ 128) = 1 / 128 := by norm_num
      rw [this]; nlinarith [hsqrt2_val, hsqrt2_nn]
    linarith [h2, h3, h4]
  -- assemble: r0 ≤ 2^126·(NE/DE) + 64/100 ≤ 2^126·Et·Mp + 64/100
  --   = 2^126·Et + 2^126·Et·(Mp−1) + 64/100 ≤ 2^126·Et + 1/10 + 64/100
  --   2^126·Et = 2^126·Ert + 2^126·(Et−Ert) ≤ 2^126·Ert + 1/50
  --   total ≤ 2^126·Ert + 1/50 + 1/10 + 64/100 = 2^126·Ert + 0.72 ≤ 2^126·Ert + 47/64
  have hNEMp : (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) ≤
      (2 ^ 126 : Real) * Et + (2 ^ 126 : Real) * Et * (Mp - 1) := by
    have h := mul_le_mul_of_nonneg_left hNEDE_le (by positivity : (0:Real) ≤ (2 ^ 126 : Real))
    nlinarith [h]
  -- final
  have hEtErt : (2 ^ 126 : Real) * Et ≤ (2 ^ 126 : Real) * Ert + 1 / 50 := by
    nlinarith [hcGap1]
  calc (r0 : Real) ≤ (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) + 64 / 100 := hr0_div
    _ ≤ ((2 ^ 126 : Real) * Et + (2 ^ 126 : Real) * Et * (Mp - 1)) + 64 / 100 := by linarith [hNEMp]
    _ ≤ ((2 ^ 126 : Real) * Et + 1 / 10) + 64 / 100 := by linarith [hcMp]
    _ ≤ (((2 ^ 126 : Real) * Ert + 1 / 50) + 1 / 10) + 64 / 100 := by linarith [hEtErt]
    _ = (2 ^ 126 : Real) * Real.exp (reducedArg x) + 19 / 25 := by rw [hErtdef]; ring



/-! ## The loose per-point real bounds (nonnegative half)

These bracket `(r0Tree x : Real)` against `2¹²⁶·exp(rt)` with loose octave-seam-absorbed constants
(`+50` over, `+701` under). They suffice for `SeamR0Bound`, whose octave-seam doubling has ~10¹¹
slack. The over side does not yet meet the per-point `MARGIN` budget — that needs the tight
cross-product sharpening; here only the loose `r0_vs_certRatio` constants are used. -/

/-- **Loose per-point never-over** (nonneg half): `r0 ≤ 2¹²⁶·exp(rt) + 50`. -/
theorem r0_real_over_loose {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    (int256 (r0Tree x) : Real) ≤ (2 ^ 126 : Real) * Real.exp (reducedArg x) + 50 := by
  obtain ⟨hover, _⟩ := r0_vs_certRatio hx hC hC0 htnn
  obtain ⟨_, hthi⟩ := tTree_in_cert_domain hx hC hC0
  set t := int256 (tTree x) with htdef
  have htdom : t ≤ (ExpCertV.H128 : Int) := by
    rw [show ((ExpCertV.H128 : Nat) : Int) = 117932881612756647068972071382077242199 from by
      unfold ExpCertV.H128; norm_num]
    exact hthi
  have hDElb := denExpV_lb hx hC hC0 htnn
  set NE := evalPoly ExpCertV.numExpV t with hNEdef
  set DE := evalPoly ExpCertV.denExpV t with hDEdef
  have hDEpos_int : (0 : Int) < DE := by
    have : (0:Int) < 2 ^ 1317 := by positivity
    linarith [hDElb, this]
  have hDEpos : (0 : Real) < (DE : Real) := by exact_mod_cast hDEpos_int
  have hoverR : (int256 (r0Tree x) : Real) * (DE : Real) <
      (2 ^ 126 : Real) * (NE : Real) + 49 * (DE : Real) := by
    have := (@Int.cast_lt Real _ _ _ _ _ _ _).mpr hover
    push_cast at this; linarith [this]
  have hr0_lt : (int256 (r0Tree x) : Real) < (2 ^ 126 : Real) * (NE : Real) / (DE : Real) + 49 := by
    rw [div_add' _ _ _ (ne_of_gt hDEpos), lt_div_iff₀ hDEpos]
    nlinarith [hoverR, hDEpos]
  have hcertlo := certLo_real htnn htdom
  have hNEnn : (0 : Real) ≤ (NE : Real) := by
    have := certNE_nonneg htnn htdom; exact_mod_cast this
  set Et := Real.exp ((t : Real) / (2 ^ 128 : Real)) with hEtdef
  have hExp_t_le_two := exp_t_le_two hx hC hC0 htnn
  rw [← hEtdef] at hExp_t_le_two
  set Mp : Real := (2 ^ 130 : Real) / ((2 ^ 130 : Real) - 1) with hMpdef
  have hNEDE_le : (NE : Real) / (DE : Real) ≤ Et * Mp := by
    have hc : ((2 ^ 130 - 1 : Int) : Real) * (NE : Real) /
        (((2 ^ 130 : Int) : Real) * (DE : Real)) ≤ Et := hcertlo
    rw [hMpdef]
    have key : (NE : Real) / (DE : Real) =
        ((2 ^ 130 : Real) / ((2 ^ 130 : Real) - 1)) *
          (((2 ^ 130 - 1 : Int) : Real) * (NE : Real) /
            (((2 ^ 130 : Int) : Real) * (DE : Real))) := by
      push_cast; field_simp; ring
    rw [key, mul_comm Et _]
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  have hclose := abs_lt.mp (reducedArg_close hx hC hC0)
  set Ert := Real.exp (reducedArg x) with hErtdef
  have hExp_diff : Et - Ert ≤ ((t : Real) / (2 ^ 128 : Real) - reducedArg x) * Et := exp_diff_le _ _
  have hgap1 : (t : Real) / (2 ^ 128 : Real) - reducedArg x < 9 / (8 * (2 ^ 128 : Real)) := by
    have := hclose.1; linarith [this]
  have hEt_nonneg : (0:Real) ≤ Et := le_of_lt (Real.exp_pos _)
  have hMp1 : Mp - 1 = 1 / ((2 ^ 130 : Real) - 1) := by rw [hMpdef]; field_simp
  have hEtMp_Ert : Et * Mp - Ert ≤
      Et * (1 / ((2 ^ 130 : Real) - 1)) + (9 / (8 * (2 ^ 128 : Real))) * Et := by
    have h1 : Et * Mp - Ert = Et * (Mp - 1) + (Et - Ert) := by ring
    rw [h1, hMp1]
    have hgap : Et - Ert ≤ (9 / (8 * (2 ^ 128 : Real))) * Et := by
      calc Et - Ert ≤ ((t : Real) / (2 ^ 128 : Real) - reducedArg x) * Et := hExp_diff
        _ ≤ (9 / (8 * (2 ^ 128 : Real))) * Et :=
            mul_le_mul_of_nonneg_right (le_of_lt hgap1) hEt_nonneg
    linarith [hgap]
  have hfinal : (2 ^ 126 : Real) * (Et * Mp) ≤ (2 ^ 126 : Real) * Ert + 1 := by
    have hb1 : Et * (1 / ((2 ^ 130 : Real) - 1)) ≤ 2 / ((2 ^ 130 : Real) - 1) := by
      rw [mul_one_div, div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith [hExp_t_le_two]
    have hb2 : (9 / (8 * (2 ^ 128 : Real))) * Et ≤ (9 / (8 * (2 ^ 128 : Real))) * 2 :=
      mul_le_mul_of_nonneg_left hExp_t_le_two (by positivity)
    have hbb : Et * Mp - Ert ≤
        2 / ((2 ^ 130 : Real) - 1) + (9 / (8 * (2 ^ 128 : Real))) * 2 := by
      linarith [hEtMp_Ert, hb1, hb2]
    have hnum : (2 ^ 126 : Real) *
        (2 / ((2 ^ 130 : Real) - 1) + (9 / (8 * (2 ^ 128 : Real))) * 2) ≤ 1 := by norm_num
    set Xb : Real := 2 / ((2 ^ 130 : Real) - 1) + (9 / (8 * (2 ^ 128 : Real))) * 2 with hXbdef
    have hscaled : (2 ^ 126 : Real) * (Et * Mp - Ert) ≤ (2 ^ 126 : Real) * Xb :=
      mul_le_mul_of_nonneg_left hbb (by positivity)
    have hdist : (2 ^ 126 : Real) * (Et * Mp - Ert) =
        (2 ^ 126 : Real) * (Et * Mp) - (2 ^ 126 : Real) * Ert := by ring
    rw [hdist] at hscaled
    linarith [hscaled, hnum]
  have hstep : (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) ≤ (2 ^ 126 : Real) * Ert + 1 :=
    le_trans (mul_le_mul_of_nonneg_left hNEDE_le (by positivity : (0:Real) ≤ (2 ^ 126 : Real))) hfinal
  have heq : (2 ^ 126 : Real) * (NE : Real) / (DE : Real) =
      (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) := by ring
  rw [heq] at hr0_lt
  linarith [hr0_lt, hstep]

/-- **Loose per-point deficit** (nonneg half): `2¹²⁶·exp(rt) ≤ r0 + 705`. -/
theorem r0_real_under_loose {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htnn : 0 ≤ int256 (tTree x)) :
    (2 ^ 126 : Real) * Real.exp (reducedArg x) ≤ (int256 (r0Tree x) : Real) + 705 := by
  obtain ⟨_, hunder⟩ := r0_vs_certRatio hx hC hC0 htnn
  obtain ⟨_, hthi⟩ := tTree_in_cert_domain hx hC hC0
  obtain ⟨_, hr0hi⟩ := r0Tree_bounds hx hC hC0
  set t := int256 (tTree x) with htdef
  have htdom : t ≤ (ExpCertV.H128 : Int) := by
    rw [show ((ExpCertV.H128 : Nat) : Int) = 117932881612756647068972071382077242199 from by
      unfold ExpCertV.H128; norm_num]
    exact hthi
  have hDElb := denExpV_lb hx hC hC0 htnn
  set NE := evalPoly ExpCertV.numExpV t with hNEdef
  set DE := evalPoly ExpCertV.denExpV t with hDEdef
  have hDEpos_int : (0 : Int) < DE := by
    have : (0:Int) < 2 ^ 1317 := by positivity
    linarith [hDElb, this]
  have hDEpos : (0 : Real) < (DE : Real) := by exact_mod_cast hDEpos_int
  -- 2^126·NE/DE < r0 + 701
  have hunderR : (2 ^ 126 : Real) * (NE : Real) <
      ((int256 (r0Tree x) : Real) + 1) * (DE : Real) + 700 * (DE : Real) := by
    have := (@Int.cast_lt Real _ _ _ _ _ _ _).mpr hunder
    push_cast at this; linarith [this]
  have hr0_gt : (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) < (int256 (r0Tree x) : Real) + 701 := by
    rw [mul_div_assoc']
    rw [div_lt_iff₀ hDEpos]
    nlinarith [hunderR, hDEpos]
  -- certUp: exp(t/2^128) ≤ (2^130+1)·NE/(2^130·DE) = (NE/DE)·M⁺⁺
  have hcertup := certUp_real htnn htdom
  have hNEnn : (0 : Real) ≤ (NE : Real) := by
    have := certNE_nonneg htnn htdom; exact_mod_cast this
  set Et := Real.exp ((t : Real) / (2 ^ 128 : Real)) with hEtdef
  set Mpp : Real := (2 ^ 130 + 1 : Real) / (2 ^ 130 : Real) with hMppdef
  have hEt_le : Et ≤ ((NE : Real) / (DE : Real)) * Mpp := by
    have hc : Et ≤ ((2 ^ 130 + 1 : Int) : Real) * (NE : Real) /
        (((2 ^ 130 : Int) : Real) * (DE : Real)) := hcertup
    rw [hMppdef]
    have key : ((NE : Real) / (DE : Real)) * ((2 ^ 130 + 1 : Real) / (2 ^ 130 : Real)) =
        ((2 ^ 130 + 1 : Int) : Real) * (NE : Real) / (((2 ^ 130 : Int) : Real) * (DE : Real)) := by
      push_cast; field_simp; ring
    rw [key]; exact hc
  -- 2^126·Et ≤ 2^126·(NE/DE)·Mpp = 2^126·(NE/DE) + 2^126·(NE/DE)·(Mpp-1).
  have hNEDE_nn : (0 : Real) ≤ (NE : Real) / (DE : Real) := div_nonneg hNEnn (le_of_lt hDEpos)
  have hMpp1 : Mpp - 1 = 1 / (2 ^ 130 : Real) := by rw [hMppdef]; field_simp
  have hr0R : (int256 (r0Tree x) : Real) < (2 ^ 128 : Real) := by
    have h := (@Int.cast_lt Real _ _ _ _ _ _ _).mpr hr0hi
    rw [show ((2 ^ 128 : Int) : Real) = (2 ^ 128 : Real) from by push_cast; ring] at h; exact h
  have hr0nn : (0 : Real) ≤ (int256 (r0Tree x) : Real) := by
    obtain ⟨hlo, _⟩ := r0Tree_bounds hx hC hC0
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hlo; push_cast at this; linarith [this]
  -- 2^126·Et ≤ r0 + 702
  have hEt_bound : (2 ^ 126 : Real) * Et ≤ (int256 (r0Tree x) : Real) + 702 := by
    have h1 : (2 ^ 126 : Real) * Et ≤ (2 ^ 126 : Real) * (((NE : Real) / (DE : Real)) * Mpp) :=
      mul_le_mul_of_nonneg_left hEt_le (by positivity)
    -- (NE/DE)·Mpp = NE/DE + (NE/DE)·(Mpp-1)
    have h2 : (2 ^ 126 : Real) * (((NE : Real) / (DE : Real)) * Mpp) =
        (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) +
          (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) * (Mpp - 1) := by ring
    -- 2^126·(NE/DE)·(Mpp-1) ≤ 1.  use 2^126·(NE/DE) < r0+701 < 2^128+701, ·2^-130 < 1
    have h3 : (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) * (Mpp - 1) ≤ 1 := by
      rw [hMpp1]
      have hpos : (0:Real) ≤ (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) :=
        mul_nonneg (by positivity) hNEDE_nn
      have hlt : (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) < (2 ^ 128 : Real) + 701 := by
        linarith [hr0_gt, hr0R]
      calc (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) * (1 / (2 ^ 130 : Real))
          ≤ ((2 ^ 128 : Real) + 701) * (1 / (2 ^ 130 : Real)) :=
            mul_le_mul_of_nonneg_right (le_of_lt hlt) (by positivity)
        _ ≤ 1 := by norm_num
    linarith [h1, h2 ▸ h1, h3, hr0_gt]
  -- gap1: 2^126·(Ert - Et) ≤ 2.25 (via convexity + exp(rt) ≤ 2)
  set Ert := Real.exp (reducedArg x) with hErtdef
  have hclose := abs_lt.mp (reducedArg_close hx hC hC0)
  have hExp_diff : Ert - Et ≤ (reducedArg x - (t : Real) / (2 ^ 128 : Real)) * Ert := exp_diff_le _ _
  have hErt_le_two := exp_reducedArg_le_two hx hC hC0
  rw [← hErtdef] at hErt_le_two
  have hErt_nn : (0:Real) ≤ Ert := le_of_lt (Real.exp_pos _)
  have hgap : Ert - Et ≤ (9 / (8 * (2 ^ 128 : Real))) * Ert := by
    have hd : reducedArg x - (t : Real) / (2 ^ 128 : Real) < 9 / (8 * (2 ^ 128 : Real)) := by
      have := hclose.2; linarith [this]
    calc Ert - Et ≤ (reducedArg x - (t : Real) / (2 ^ 128 : Real)) * Ert := hExp_diff
      _ ≤ (9 / (8 * (2 ^ 128 : Real))) * Ert := mul_le_mul_of_nonneg_right (le_of_lt hd) hErt_nn
  have hgap126 : (2 ^ 126 : Real) * (Ert - Et) ≤ 3 := by
    have h1 : (2 ^ 126 : Real) * (Ert - Et) ≤ (2 ^ 126 : Real) * ((9 / (8 * (2 ^ 128 : Real))) * Ert) :=
      mul_le_mul_of_nonneg_left hgap (by positivity)
    have h2 : (2 ^ 126 : Real) * ((9 / (8 * (2 ^ 128 : Real))) * Ert) ≤
        (2 ^ 126 : Real) * ((9 / (8 * (2 ^ 128 : Real))) * 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hErt_le_two (by positivity)) (by positivity)
    have h3 : (2 ^ 126 : Real) * ((9 / (8 * (2 ^ 128 : Real))) * 2) ≤ 3 := by norm_num
    linarith [h1, h2, h3]
  -- assemble: 2^126·Ert = 2^126·Et + 2^126·(Ert-Et) ≤ (r0+702) + 3
  have hdist : (2 ^ 126 : Real) * Ert = (2 ^ 126 : Real) * Et + (2 ^ 126 : Real) * (Ert - Et) := by ring
  rw [hdist]
  linarith [hEt_bound, hgap126]

/-! ## The loose per-point real bounds (negative half) -/

/-- `t/2¹²⁸ ≤ 0` and the cert domain `−t ≤ H128` for the negative half. -/
theorem tdom_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) : (-(int256 (tTree x))) ≤ (ExpCertV.H128 : Int) := by
  obtain ⟨htlo, _⟩ := tTree_in_cert_domain hx hC hC0
  rw [show ((ExpCertV.H128 : Nat) : Int) = 117932881612756647068972071382077242199 from by
    unfold ExpCertV.H128; norm_num]
  omega

/-- **Loose per-point never-over** (negative half): `r0 ≤ 2¹²⁶·exp(rt) + 152`. -/
theorem r0_real_over_loose_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) :
    (int256 (r0Tree x) : Real) ≤ (2 ^ 126 : Real) * Real.exp (reducedArg x) + 152 := by
  obtain ⟨hover, _⟩ := r0_vs_certRatio_neg hx hC hC0 htneg
  have htdom := tdom_neg hx hC hC0 htneg
  set t := int256 (tTree x) with htdef
  have hDElb := denExpV_lb_neg hx hC hC0 htneg
  set NE := evalPoly ExpCertV.numExpV t with hNEdef
  set DE := evalPoly ExpCertV.denExpV t with hDEdef
  have hDEpos_int : (0 : Int) < DE := by
    have : (0:Int) < 2 ^ 1317 := by positivity
    linarith [hDElb, this]
  have hDEpos : (0 : Real) < (DE : Real) := by exact_mod_cast hDEpos_int
  obtain ⟨hNEpos, _⟩ := certNE_pos_neg_aux htneg htdom
  have hNEnn : (0 : Real) ≤ (NE : Real) := by have : (0:Int) ≤ NE := le_of_lt hNEpos
                                              exact_mod_cast this
  have hoverR : (int256 (r0Tree x) : Real) * (DE : Real) <
      (2 ^ 126 : Real) * (NE : Real) + 150 * (DE : Real) := by
    have := (@Int.cast_lt Real _ _ _ _ _ _ _).mpr hover
    push_cast at this; linarith [this]
  have hr0_lt : (int256 (r0Tree x) : Real) < (2 ^ 126 : Real) * (NE : Real) / (DE : Real) + 150 := by
    rw [div_add' _ _ _ (ne_of_gt hDEpos), lt_div_iff₀ hDEpos]
    nlinarith [hoverR, hDEpos]
  -- NE/DE ≤ exp(t/2^128)·M⁺⁺ from certLo_real_neg
  have hcl := certLo_real_neg htneg htdom
  set Et := Real.exp ((t : Real) / (2 ^ 128 : Real)) with hEtdef
  set Mpp : Real := (2 ^ 130 + 1 : Real) / (2 ^ 130 : Real) with hMppdef
  have hNEDE_le : (NE : Real) / (DE : Real) ≤ Et * Mpp := by
    -- hcl: 2^130·NE/((2^130+1)·DE) ≤ Et ⇒ NE/DE ≤ Et·(2^130+1)/2^130
    rw [hMppdef]
    have key : (NE : Real) / (DE : Real) =
        ((2 ^ 130 + 1 : Real) / (2 ^ 130 : Real)) *
          (((2 ^ 130 : Int) : Real) * (NE : Real) /
            (((2 ^ 130 + 1 : Int) : Real) * (DE : Real))) := by
      push_cast; field_simp; ring
    rw [key, mul_comm Et _]
    exact mul_le_mul_of_nonneg_left hcl (by positivity)
  -- exp(t/2^128) ≤ 1 (t ≤ 0) and exp(rt) bound
  have hEt_le_one : Et ≤ 1 := by
    rw [hEtdef]
    have : (t : Real) / (2 ^ 128 : Real) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      exact_mod_cast htneg
    calc Real.exp ((t : Real) / (2 ^ 128 : Real)) ≤ Real.exp 0 := Real.exp_le_exp.mpr this
      _ = 1 := Real.exp_zero
  have hEt_nonneg : (0:Real) ≤ Et := le_of_lt (Real.exp_pos _)
  have hclose := abs_lt.mp (reducedArg_close hx hC hC0)
  set Ert := Real.exp (reducedArg x) with hErtdef
  have hExp_diff : Et - Ert ≤ ((t : Real) / (2 ^ 128 : Real) - reducedArg x) * Et := exp_diff_le _ _
  have hgap1 : (t : Real) / (2 ^ 128 : Real) - reducedArg x < 9 / (8 * (2 ^ 128 : Real)) := by
    have := hclose.1; linarith [this]
  have hMp1 : Mpp - 1 = 1 / (2 ^ 130 : Real) := by rw [hMppdef]; field_simp
  have hfinal : (2 ^ 126 : Real) * (Et * Mpp) ≤ (2 ^ 126 : Real) * Ert + 1 := by
    have hEtMp_Ert : Et * Mpp - Ert ≤
        Et * (1 / (2 ^ 130 : Real)) + (9 / (8 * (2 ^ 128 : Real))) * Et := by
      have h1 : Et * Mpp - Ert = Et * (Mpp - 1) + (Et - Ert) := by ring
      rw [h1, hMp1]
      have hgap : Et - Ert ≤ (9 / (8 * (2 ^ 128 : Real))) * Et := by
        calc Et - Ert ≤ ((t : Real) / (2 ^ 128 : Real) - reducedArg x) * Et := hExp_diff
          _ ≤ (9 / (8 * (2 ^ 128 : Real))) * Et :=
              mul_le_mul_of_nonneg_right (le_of_lt hgap1) hEt_nonneg
      linarith [hgap]
    have hb1 : Et * (1 / (2 ^ 130 : Real)) ≤ 1 / (2 ^ 130 : Real) := by
      rw [mul_one_div, div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith [hEt_le_one]
    have hb2 : (9 / (8 * (2 ^ 128 : Real))) * Et ≤ (9 / (8 * (2 ^ 128 : Real))) * 1 :=
      mul_le_mul_of_nonneg_left hEt_le_one (by positivity)
    set Xb : Real := 1 / (2 ^ 130 : Real) + (9 / (8 * (2 ^ 128 : Real))) * 1 with hXbdef
    have hbb : Et * Mpp - Ert ≤ Xb := by rw [hXbdef]; linarith [hEtMp_Ert, hb1, hb2]
    have hnum : (2 ^ 126 : Real) * Xb ≤ 1 := by rw [hXbdef]; norm_num
    have hscaled : (2 ^ 126 : Real) * (Et * Mpp - Ert) ≤ (2 ^ 126 : Real) * Xb :=
      mul_le_mul_of_nonneg_left hbb (by positivity)
    have hdist : (2 ^ 126 : Real) * (Et * Mpp - Ert) =
        (2 ^ 126 : Real) * (Et * Mpp) - (2 ^ 126 : Real) * Ert := by ring
    rw [hdist] at hscaled; linarith [hscaled, hnum]
  have hstep : (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) ≤ (2 ^ 126 : Real) * Ert + 1 :=
    le_trans (mul_le_mul_of_nonneg_left hNEDE_le (by positivity : (0:Real) ≤ (2 ^ 126 : Real))) hfinal
  have heq : (2 ^ 126 : Real) * (NE : Real) / (DE : Real) =
      (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) := by ring
  rw [heq] at hr0_lt
  linarith [hr0_lt, hstep]

/-- **Loose per-point deficit** (negative half): `2¹²⁶·exp(rt) ≤ r0 + 705`. -/
theorem r0_real_under_loose_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) :
    (2 ^ 126 : Real) * Real.exp (reducedArg x) ≤ (int256 (r0Tree x) : Real) + 705 := by
  obtain ⟨_, hunder⟩ := r0_vs_certRatio_neg hx hC hC0 htneg
  obtain ⟨_, hr0hi⟩ := r0Tree_bounds hx hC hC0
  have htdom := tdom_neg hx hC hC0 htneg
  set t := int256 (tTree x) with htdef
  have hDElb := denExpV_lb_neg hx hC hC0 htneg
  set NE := evalPoly ExpCertV.numExpV t with hNEdef
  set DE := evalPoly ExpCertV.denExpV t with hDEdef
  have hDEpos_int : (0 : Int) < DE := by
    have : (0:Int) < 2 ^ 1317 := by positivity
    linarith [hDElb, this]
  have hDEpos : (0 : Real) < (DE : Real) := by exact_mod_cast hDEpos_int
  obtain ⟨hNEpos, _⟩ := certNE_pos_neg_aux htneg htdom
  have hNEnn : (0 : Real) ≤ (NE : Real) := by have : (0:Int) ≤ NE := le_of_lt hNEpos
                                              exact_mod_cast this
  have hunderR : (2 ^ 126 : Real) * (NE : Real) <
      ((int256 (r0Tree x) : Real) + 1) * (DE : Real) + 700 * (DE : Real) := by
    have := (@Int.cast_lt Real _ _ _ _ _ _ _).mpr hunder
    push_cast at this; linarith [this]
  have hr0_gt : (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) < (int256 (r0Tree x) : Real) + 701 := by
    rw [mul_div_assoc']; rw [div_lt_iff₀ hDEpos]
    nlinarith [hunderR, hDEpos]
  -- certUp_real_neg: exp(t/2^128) ≤ (NE/DE)·M⁺
  have hcu := certUp_real_neg htneg htdom
  set Et := Real.exp ((t : Real) / (2 ^ 128 : Real)) with hEtdef
  set Mp : Real := (2 ^ 130 : Real) / ((2 ^ 130 : Real) - 1) with hMpdef
  have hEt_le : Et ≤ ((NE : Real) / (DE : Real)) * Mp := by
    rw [hMpdef]
    have key : ((NE : Real) / (DE : Real)) * ((2 ^ 130 : Real) / ((2 ^ 130 : Real) - 1)) =
        ((2 ^ 130 : Int) : Real) * (NE : Real) /
          (((2 ^ 130 - 1 : Int) : Real) * (DE : Real)) := by
      push_cast; field_simp; ring
    rw [key]; exact hcu
  have hNEDE_nn : (0 : Real) ≤ (NE : Real) / (DE : Real) := div_nonneg hNEnn (le_of_lt hDEpos)
  have hMp1 : Mp - 1 = 1 / ((2 ^ 130 : Real) - 1) := by rw [hMpdef]; field_simp
  have hr0R : (int256 (r0Tree x) : Real) < (2 ^ 128 : Real) := by
    have h := (@Int.cast_lt Real _ _ _ _ _ _ _).mpr hr0hi
    rw [show ((2 ^ 128 : Int) : Real) = (2 ^ 128 : Real) from by push_cast; ring] at h; exact h
  have hEt_bound : (2 ^ 126 : Real) * Et ≤ (int256 (r0Tree x) : Real) + 702 := by
    have h1 : (2 ^ 126 : Real) * Et ≤ (2 ^ 126 : Real) * (((NE : Real) / (DE : Real)) * Mp) :=
      mul_le_mul_of_nonneg_left hEt_le (by positivity)
    have h2 : (2 ^ 126 : Real) * (((NE : Real) / (DE : Real)) * Mp) =
        (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) +
          (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) * (Mp - 1) := by ring
    have h3 : (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) * (Mp - 1) ≤ 1 := by
      rw [hMp1]
      have hlt : (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) < (2 ^ 128 : Real) + 701 := by
        linarith [hr0_gt, hr0R]
      have hpos : (0:Real) ≤ (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) :=
        mul_nonneg (by positivity) hNEDE_nn
      calc (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) * (1 / ((2 ^ 130 : Real) - 1))
          ≤ ((2 ^ 128 : Real) + 701) * (1 / ((2 ^ 130 : Real) - 1)) :=
            mul_le_mul_of_nonneg_right (le_of_lt hlt) (by positivity)
        _ ≤ 1 := by norm_num
    linarith [h1, h2 ▸ h1, h3, hr0_gt]
  set Ert := Real.exp (reducedArg x) with hErtdef
  have hclose := abs_lt.mp (reducedArg_close hx hC hC0)
  have hExp_diff : Ert - Et ≤ (reducedArg x - (t : Real) / (2 ^ 128 : Real)) * Ert := exp_diff_le _ _
  have hErt_le_two := exp_reducedArg_le_two hx hC hC0
  rw [← hErtdef] at hErt_le_two
  have hErt_nn : (0:Real) ≤ Ert := le_of_lt (Real.exp_pos _)
  have hgap : Ert - Et ≤ (9 / (8 * (2 ^ 128 : Real))) * Ert := by
    have hd : reducedArg x - (t : Real) / (2 ^ 128 : Real) < 9 / (8 * (2 ^ 128 : Real)) := by
      have := hclose.2; linarith [this]
    calc Ert - Et ≤ (reducedArg x - (t : Real) / (2 ^ 128 : Real)) * Ert := hExp_diff
      _ ≤ (9 / (8 * (2 ^ 128 : Real))) * Ert := mul_le_mul_of_nonneg_right (le_of_lt hd) hErt_nn
  have hgap126 : (2 ^ 126 : Real) * (Ert - Et) ≤ 3 := by
    have h1 : (2 ^ 126 : Real) * (Ert - Et) ≤ (2 ^ 126 : Real) * ((9 / (8 * (2 ^ 128 : Real))) * Ert) :=
      mul_le_mul_of_nonneg_left hgap (by positivity)
    have h2 : (2 ^ 126 : Real) * ((9 / (8 * (2 ^ 128 : Real))) * Ert) ≤
        (2 ^ 126 : Real) * ((9 / (8 * (2 ^ 128 : Real))) * 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hErt_le_two (by positivity)) (by positivity)
    have h3 : (2 ^ 126 : Real) * ((9 / (8 * (2 ^ 128 : Real))) * 2) ≤ 3 := by norm_num
    linarith [h1, h2, h3]
  have hdist : (2 ^ 126 : Real) * Ert = (2 ^ 126 : Real) * Et + (2 ^ 126 : Real) * (Ert - Et) := by ring
  rw [hdist]
  linarith [hEt_bound, hgap126]

/-! ## The combined per-point real bounds (both signs)

Case-splitting on the sign of the reduced argument unifies the two halves into loose octave-seam
brackets valid for every meaningful-region input. -/

/-- **Per-point never-over** (any sign): `r0 ≤ 2¹²⁶·exp(rt) + 152`. -/
theorem r0_real_over {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (int256 (r0Tree x) : Real) ≤ (2 ^ 126 : Real) * Real.exp (reducedArg x) + 152 := by
  rcases le_or_gt 0 (int256 (tTree x)) with htnn | htneg
  · linarith [r0_real_over_loose hx hC hC0 htnn]
  · exact r0_real_over_loose_neg hx hC hC0 (le_of_lt htneg)

/-- **Per-point deficit** (any sign): `2¹²⁶·exp(rt) ≤ r0 + 705`. -/
theorem r0_real_under {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (2 ^ 126 : Real) * Real.exp (reducedArg x) ≤ (int256 (r0Tree x) : Real) + 705 := by
  rcases le_or_gt 0 (int256 (tTree x)) with htnn | htneg
  · exact r0_real_under_loose hx hC hC0 htnn
  · exact r0_real_under_loose_neg hx hC hC0 (le_of_lt htneg)

/-! ## The tight joint per-point never-over (negative half + combined) -/

theorem exp_t_ge_inv_sqrt2 {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (Real.sqrt 2)⁻¹ ≤ Real.exp ((int256 (tTree x) : Real) / (2 ^ 128 : Real)) := by
  obtain ⟨htlo, _⟩ := tTree_in_cert_domain hx hC hC0
  -- t/2^128 ≥ -H128/2^128 ≥ -log2/2
  have hp128 : (0 : Real) < (2 ^ 128 : Real) := by positivity
  have htR : -(117932881612756647068972071382077242199 : Real) ≤ (int256 (tTree x) : Real) := by
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr htlo; push_cast at this; linarith [this]
  -- -log2/2 ≤ t/2^128:  2·H128 ≤ log2·2^128 (from log2 ≥ LN2/2^235)
  have hln2lo := ln2_lower; rw [LN2c_eq] at hln2lo
  have hkey : (2 : Real) * (117932881612756647068972071382077242199 : Real) ≤ Real.log 2 * (2 ^ 128 : Real) := by
    have h1 : (38271408169742254668347313025622401492114385419650052359639581444463709 : Real) / (2 ^ 235 : Real) * (2 ^ 128 : Real) ≤ Real.log 2 * (2 ^ 128 : Real) :=
      mul_le_mul_of_nonneg_right hln2lo (by positivity)
    have h2 : (2 : Real) * (117932881612756647068972071382077242199 : Real) ≤
        (38271408169742254668347313025622401492114385419650052359639581444463709 : Real) / (2 ^ 235 : Real) * (2 ^ 128 : Real) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:Real) < 2 ^ 235)]; norm_num
    linarith [h1, h2]
  have hge : -(Real.log 2 / 2) ≤ (int256 (tTree x) : Real) / (2 ^ 128 : Real) := by
    have hmul : -(Real.log 2 / 2) * (2 ^ 128 : Real) ≤ (int256 (tTree x) : Real) := by
      nlinarith [htR, hkey]
    exact (le_div_iff₀ hp128).mpr hmul
  have hexpsq : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0:Real) < 2)]
    congr 1; ring
  have hsq : (Real.sqrt 2)⁻¹ = Real.exp (-(Real.log 2 / 2)) := by
    rw [Real.exp_neg, hexpsq]
  rw [hsq]
  exact Real.exp_le_exp.mpr hge

-- exp(rt) ≥ 7/10 on the region (rt = t/2^128 + (rt − t/2^128); exp(t/2^128) ≥ 1/√2, the gap is tiny).

theorem exp_reducedArg_ge_07 {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (7 : Real) / 10 ≤ Real.exp (reducedArg x) := by
  have hge := exp_t_ge_inv_sqrt2 hx hC hC0
  have hclose := abs_lt.mp (reducedArg_close hx hC hC0)
  set t := int256 (tTree x) with htdef
  -- exp(rt) = exp(t/2^128)·exp(rt − t/2^128) ≥ (1/√2)·exp(rt − t/2^128)
  have hsplit : Real.exp (reducedArg x) =
      Real.exp ((t : Real) / (2 ^ 128 : Real)) * Real.exp (reducedArg x - (t : Real) / (2 ^ 128 : Real)) := by
    rw [← Real.exp_add]; congr 1; ring
  -- exp(rt − t/2^128) ≥ 1 + (rt − t/2^128) ≥ 1 − 9/(8·2^128)
  have hgap : reducedArg x - (t : Real) / (2 ^ 128 : Real) > -(9 / (8 * (2 ^ 128 : Real))) := by
    have := hclose.1; linarith [this]
  have hconv : (1 : Real) - 9 / (8 * (2 ^ 128 : Real)) ≤ Real.exp (reducedArg x - (t : Real) / (2 ^ 128 : Real)) := by
    have h := Real.add_one_le_exp (reducedArg x - (t : Real) / (2 ^ 128 : Real))
    linarith [h, hgap]
  -- √2⁻¹ ≥ 7071/10000 (⟺ √2 ≤ 10000/7071, since (10000/7071)² > 2)
  have hsqrt2_pos : (0:Real) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2_le : Real.sqrt 2 ≤ 10000 / 7071 := by
    rw [Real.sqrt_le_iff]; constructor <;> norm_num
  have hinvsqrt2 : (7071 : Real) / 10000 ≤ (Real.sqrt 2)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hsqrt2_pos]
    calc Real.sqrt 2 ≤ 10000 / 7071 := hsqrt2_le
      _ = (7071 / 10000)⁻¹ := by norm_num
  have hgap_small : (1 : Real) - 9 / (8 * (2 ^ 128 : Real)) ≥ 9999 / 10000 := by
    have : (9 : Real) / (8 * (2 ^ 128 : Real)) ≤ 1 / 10000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; norm_num
    linarith [this]
  rw [hsplit]
  have hpos : (0:Real) ≤ Real.exp (reducedArg x - (t : Real) / (2 ^ 128 : Real)) := le_of_lt (Real.exp_pos _)
  calc (7:Real)/10 ≤ (7071/10000) * (9999/10000) := by norm_num
    _ ≤ (Real.sqrt 2)⁻¹ * (1 - 9 / (8 * (2 ^ 128 : Real))) := by
        apply mul_le_mul hinvsqrt2 (by linarith [hgap_small]) (by norm_num) (by positivity)
    _ ≤ Real.exp ((t : Real) / (2 ^ 128 : Real)) * Real.exp (reducedArg x - (t : Real) / (2 ^ 128 : Real)) := by
        apply mul_le_mul hge hconv (by positivity) (le_of_lt (Real.exp_pos _))


-- num ≥ (2/3)·den for t ≤ 0:  r0 ≤ 2^126·num/den (floor), r0 ≥ 2^126·exp(rt)−705 > (2/3)·2^126.

theorem num_ge_23_den {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    2 * ((evTree x : Int) - int256 (todTree x)) ≤ 3 * ((evTree x : Int) + int256 (todTree x)) := by
  obtain ⟨hfloor_lo, _⟩ := r0_floor_sandwich hx hC hC0
  have hu := r0_real_under hx hC hC0
  have hge07 := exp_reducedArg_ge_07 hx hC hC0
  set num := (evTree x : Int) + int256 (todTree x) with hnumdef
  set den := (evTree x : Int) - int256 (todTree x) with hdendef
  have hden072 : (61251667550081741634933722430035858604 : Int) ≤ den := den_ge_072 hx hC hC0
  have hdenpos : (0:Int) < den := lt_of_lt_of_le (by norm_num) hden072
  have hdenR : (0:Real) < (den : Real) := by exact_mod_cast hdenpos
  have hr0R : (2 ^ 126 : Real) * (7/10) - 705 ≤ (int256 (r0Tree x) : Real) := by
    have h1 : (2 ^ 126 : Real) * (7/10) ≤ (2 ^ 126 : Real) * Real.exp (reducedArg x) :=
      mul_le_mul_of_nonneg_left hge07 (by positivity)
    linarith [hu, h1]
  have hflR : (int256 (r0Tree x) : Real) * (den : Real) ≤ (2 ^ 126 : Real) * (num : Real) := by
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hfloor_lo; push_cast at this; linarith [this]
  have hnumden : (2 ^ 126 : Real) * (7/10) * (den : Real) - 705 * (den : Real) ≤ (2 ^ 126 : Real) * (num : Real) := by
    nlinarith [hr0R, hflR, hdenR]
  have hkey : (2 : Real) * (den : Real) ≤ 3 * (num : Real) := by
    have hp : (0:Real) < (2 ^ 126 : Real) := by positivity
    have hnum_ge : (7/10) * (den : Real) - 705 * (den : Real) / (2 ^ 126 : Real) ≤ (num : Real) := by
      rw [← mul_le_mul_left hp]
      have heq : (2 ^ 126 : Real) * ((7/10) * (den : Real) - 705 * (den : Real) / (2 ^ 126 : Real)) =
          (2 ^ 126 : Real) * (7/10) * (den : Real) - 705 * (den : Real) := by field_simp; ring
      rw [heq]; exact hnumden
    have hden_big : (705 : Real) * (den : Real) / (2 ^ 126 : Real) ≤ (1/100) * (den : Real) := by
      rw [div_le_iff₀ hp]
      nlinarith [hdenR, hden072, (by norm_num : (0:Real) < (2:Real)^126)]
    nlinarith [hnum_ge, hden_big, hdenR]
  have : ((2 * den : Int) : Real) ≤ ((3 * num : Int) : Real) := by push_cast; linarith [hkey]
  exact_mod_cast this


-- The integer cR bound (negative half): 100·W_od·2^1039·(−t)·(r0+2^126) ≤ 64·DE.
-- Chain (multiplied by od·den > 0): (−t)·od ≤ 2^128·(−tod); (r0+2^126)·den ≤ 2^127·ev;
-- (−tod)·ev = (den²−num²)/4 ≤ 5·den²/36 (from 3·num ≥ 2·den ⟹ 9·num² ≥ 4·den²); od ≥ B4; DE ≥ 2^1193(den−2).

theorem todNumV_lb_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) :
    2 ^ 1193 * (int256 (todTree x)) + 69402657 * 2 ^ 1039 * (int256 (tTree x)) ≤
      evalPoly ExpCertV.todNumV (int256 (tTree x)) := by
  obtain ⟨_, _, htodlo, _⟩ := todTree_bound hx hC hC0
  obtain ⟨hodlo, hodhi⟩ := odNumVPoly_bracket hx hC hC0
  set t := int256 (tTree x) with htdef
  rw [evalTodNumV]
  -- todP = 2^23·t·odpoly.  t ≤ 0, odpoly < 2^1042·od + W_od·2^1016 ⟹ 2^23·t·odpoly ≥ 2^23·t·(2^1042 od + W_od 2^1016)
  have hmul : 2 ^ 23 * (t * (2 ^ 1042 * (odTree x : Int) + 69402657 * 2 ^ 1016)) ≤
      2 ^ 23 * (t * evalPoly ExpCertV.odNumVPoly t) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonpos_left (le_of_lt hodhi) htneg
  -- 2^23·t·(2^1042 od + W_od 2^1016) = 2^1065·(t·od) + W_od·2^1039·t ≥ 2^1193·tod + W_od·2^1039·t
  have htod_lo : (2 ^ 128 : Int) * (int256 (todTree x)) ≤ t * (odTree x : Int) := htodlo
  have key : 2 ^ 1193 * (int256 (todTree x)) + 69402657 * 2 ^ 1039 * t ≤
      2 ^ 23 * (t * (2 ^ 1042 * (odTree x : Int) + 69402657 * 2 ^ 1016)) := by
    have e1 : 2 ^ 23 * (t * (2 ^ 1042 * (odTree x : Int) + 69402657 * 2 ^ 1016)) =
        2 ^ 1065 * (t * (odTree x : Int)) + 69402657 * 2 ^ 1039 * t := by ring
    have e2 : (2 : Int) ^ 1065 * ((2 ^ 128 : Int) * (int256 (todTree x))) = 2 ^ 1193 * (int256 (todTree x)) := by
      rw [show (2:Int) ^ 1193 = 2 ^ 1065 * 2 ^ 128 from by rw [← pow_add]]; ring
    rw [e1]
    have h := mul_le_mul_of_nonneg_left htod_lo (by positivity : (0:Int) ≤ 2 ^ 1065)
    nlinarith [h, e2]
  linarith [hmul, key]

/-- **Negative-half joint cert-ratio over** (`t ≤ 0`): `r0·DE − 2¹²⁶·NE ≤ W_od·2¹⁰³⁹·|t|·(r0+2¹²⁶)`.
The even truncation `Ee·(r0−2¹²⁶) ≤ 0` (since `r0 < 2¹²⁶`) is dropped; the binding term is the odd
truncation, attenuated to the `t`-scale by `W_od·2¹⁰³⁹·t`. -/

theorem r0_certRatio_over_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) :
    int256 (r0Tree x) * evalPoly ExpCertV.denExpV (int256 (tTree x)) -
        2 ^ 126 * evalPoly ExpCertV.numExpV (int256 (tTree x)) ≤
      69402657 * 2 ^ 1039 * (-(int256 (tTree x))) * (int256 (r0Tree x) + 2 ^ 126) := by
  obtain ⟨hfloor_lo, _⟩ := r0_floor_sandwich hx hC hC0
  obtain ⟨hevlo, _⟩ := evNumVPoly_bracket hx hC hC0
  have htodlb := todNumV_lb_neg hx hC hC0 htneg
  rw [evalNumExpV, evalDenExpV]
  set t := int256 (tTree x) with htdef
  set r0 := int256 (r0Tree x) with hr0def
  set ev := (evTree x : Int) with hevdef
  set tod := int256 (todTree x) with htoddef
  set evP := evalPoly ExpCertV.evNumVPoly t with hevP
  set todP := evalPoly ExpCertV.todNumV t with htodP
  obtain ⟨hr0lo, _⟩ := r0Tree_bounds hx hC hC0
  have hr0nn : (0:Int) ≤ r0 := by linarith [hr0lo]
  -- tod ≤ 0 for t ≤ 0 (tod = ⌊t·od/2^128⌋, t ≤ 0, od ≥ 0)
  have hodnn : (0:Int) ≤ (odTree x : Int) := Int.natCast_nonneg _
  have htod_np : tod ≤ 0 := by
    obtain ⟨_, _, htodlo, _⟩ := todTree_bound hx hC hC0
    -- 2^128·tod ≤ t·od ≤ 0
    have htod_nonpos : (2 ^ 128 : Int) * tod ≤ 0 := le_trans htodlo (mul_nonpos_of_nonpos_of_nonneg htneg hodnn)
    have h2 : (2 ^ 128 : Int) * tod ≤ 2 ^ 128 * 0 := by simpa using htod_nonpos
    exact le_of_mul_le_mul_left h2 (by norm_num)
  -- r0 ≤ 2^126: r0·den ≤ 2^126·num ≤ 2^126·den (num ≤ den ⟺ tod ≤ 0); den > 0
  have hdenpos : (0:Int) < ev - tod := by
    have := den_ge_072 hx hC hC0; rw [← hevdef, ← htoddef] at this
    linarith [this, (by norm_num : (0:Int) < 61251667550081741634933722430035858604)]
  have hr0le126 : r0 ≤ 2 ^ 126 := by
    have hnumden : r0 * (ev - tod) ≤ 2 ^ 126 * (ev - tod) := by
      have h1 : r0 * (ev - tod) ≤ 2 ^ 126 * (ev + tod) := hfloor_lo
      nlinarith [h1, htod_np, (by positivity : (0:Int) ≤ (2:Int)^126)]
    have := le_of_mul_le_mul_right hnumden hdenpos
    exact this
  have hr0m_np : r0 - 2 ^ 126 ≤ 0 := by linarith [hr0le126]
  have hr0p_nn : (0:Int) ≤ r0 + 2 ^ 126 := by positivity
  -- evP·(r0−2^126) ≤ 2^1193·ev·(r0−2^126)   [evP ≥ 2^1193 ev, r0−2^126 ≤ 0]
  have hterm1 : evP * (r0 - 2 ^ 126) ≤ 2 ^ 1193 * ev * (r0 - 2 ^ 126) :=
    mul_le_mul_of_nonpos_right hevlo hr0m_np
  -- −todP·(r0+2^126) ≤ −(2^1193·tod + W_od·2^1039·t)·(r0+2^126)   [todP ≥ lower, r0+2^126 ≥ 0]
  have hterm2 : -(todP * (r0 + 2 ^ 126)) ≤ -((2 ^ 1193 * tod + 69402657 * 2 ^ 1039 * t) * (r0 + 2 ^ 126)) := by
    have := mul_le_mul_of_nonneg_right htodlb hr0p_nn
    linarith [this]
  -- floor: 2^1193·(den·r0 − 2^126·num) ≤ 0
  have hfloor : r0 * (ev - tod) - 2 ^ 126 * (ev + tod) ≤ 0 := by linarith [hfloor_lo]
  have hfloor1193 : (2 ^ 1193 : Int) * (r0 * (ev - tod) - 2 ^ 126 * (ev + tod)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hfloor
  -- assemble: the goal LHS is evP·(r0−2^126) − todP·(r0+2^126); the bound terms collapse via the floor
  have hid1 : r0 * (evP - todP) - 2 ^ 126 * (evP + todP) = evP * (r0 - 2 ^ 126) - todP * (r0 + 2 ^ 126) := by ring
  have hid2 : 2 ^ 1193 * ev * (r0 - 2 ^ 126) - (2 ^ 1193 * tod + 69402657 * 2 ^ 1039 * t) * (r0 + 2 ^ 126)
      = 2 ^ 1193 * (r0 * (ev - tod) - 2 ^ 126 * (ev + tod)) + 69402657 * 2 ^ 1039 * (-t) * (r0 + 2 ^ 126) := by
    ring
  rw [hid1]
  linarith [hterm1, hterm2, hfloor1193, hid2]

/-- **The joint per-point never-over (negative half).** `r0 ≤ 2¹²⁶·exp(rt) + 19/25` for `t ≤ 0`. -/

theorem r0_certRatio_over_neg_bound {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) :
    100 * (69402657 * 2 ^ 1039 * (-(int256 (tTree x))) * (int256 (r0Tree x) + 2 ^ 126)) ≤
      64 * evalPoly ExpCertV.denExpV (int256 (tTree x)) := by
  obtain ⟨_, _, htodlo, _⟩ := todTree_bound hx hC hC0
  obtain ⟨hfloor_lo, _⟩ := r0_floor_sandwich hx hC hC0
  obtain ⟨hdenlo, _⟩ := denExpV_bracket_neg hx hC hC0 htneg
  set t := int256 (tTree x) with htdef
  set r0 := int256 (r0Tree x) with hr0def
  set ev := (evTree x : Int) with hevdef
  set tod := int256 (todTree x) with htoddef
  set od := (odTree x : Int) with hoddef
  set DE := evalPoly ExpCertV.denExpV t with hDEdef
  -- basic facts
  have hodB4 : (51893481707599524783927774179503442518 : Int) ≤ od := by
    -- od ≥ B4 (odd leading constant; odTree = B4 + nonneg shifts)
    have : (0x270a522f476182f119f08da0ba710a56 : Nat) ≤ odTree x := odTree_ge (vTree_eq hx hC hC0).2
    have h := (@Int.ofNat_le _ _).mpr this
    rw [show ((0x270a522f476182f119f08da0ba710a56 : Nat) : Int) = 51893481707599524783927774179503442518 from by norm_num] at h
    rw [hoddef]; exact_mod_cast h
  have hodpos : (0:Int) < od := lt_of_lt_of_le (by norm_num) hodB4
  have htnp : t ≤ 0 := htneg
  have hntnn : (0:Int) ≤ -t := by omega
  -- tod ≤ 0
  have hodnn : (0:Int) ≤ od := le_of_lt hodpos
  have htod_np : tod ≤ 0 := by
    have hle : (2 ^ 128 : Int) * tod ≤ t * od := htodlo
    have hp : t * od ≤ 0 := mul_nonpos_of_nonpos_of_nonneg htnp hodnn
    have h2 : (2 ^ 128 : Int) * tod ≤ 2 ^ 128 * 0 := by simpa using le_trans hle hp
    exact le_of_mul_le_mul_left h2 (by norm_num)
  have hntodnn : (0:Int) ≤ -tod := by omega
  -- den := ev - tod > 0; den ≥ 0.72·2^126
  have hden072 : (61251667550081741634933722430035858604 : Int) ≤ ev - tod := by
    have := den_ge_072 hx hC hC0; rw [← hevdef, ← htoddef] at this; exact this
  have hdenpos : (0:Int) < ev - tod := lt_of_lt_of_le (by norm_num) hden072
  -- (1) (−t)·od ≤ 2^128·(−tod):  2^128·tod ≤ t·od ⟹ −t·od ≤ −2^128·tod = 2^128·(−tod)
  have hstep1 : (-t) * od ≤ 2 ^ 128 * (-tod) := by
    have hle : (2 ^ 128 : Int) * tod ≤ t * od := htodlo
    have he : (-t) * od = -(t * od) := by ring
    have he2 : (2:Int) ^ 128 * (-tod) = -(2 ^ 128 * tod) := by ring
    rw [he, he2]; linarith [hle]
  -- (2) (r0+2^126)·(ev−tod) ≤ 2^127·ev:  r0·(ev−tod) ≤ 2^126·(ev+tod) (floor), +2^126·(ev−tod)
  have hstep2 : (r0 + 2 ^ 126) * (ev - tod) ≤ 2 ^ 127 * ev := by
    have hfl : r0 * (ev - tod) ≤ 2 ^ 126 * (ev + tod) := hfloor_lo
    nlinarith [hfl]
  -- (3) 9·num² ≥ 4·den²  from 3·num ≥ 2·den (num=ev+tod ≥ 0, den=ev−tod > 0)
  have h32 := num_ge_23_den hx hC hC0
  have h32' : 2 * (ev - tod) ≤ 3 * (ev + tod) := by rw [← hevdef, ← htoddef] at h32; exact h32
  have hnumnn : (0:Int) ≤ ev + tod := by
    obtain ⟨hevlo, _⟩ := evTree_facts (vTree_eq hx hC hC0).2
    obtain ⟨htod_lo, _, _, _⟩ := todTree_bound hx hC hC0
    have he : (103786963415199049567855548359006885036 : Int) ≤ ev := by rw [hevdef]; exact_mod_cast hevlo
    have ht : -(2 ^ 125 : Int) ≤ tod := htod_lo
    have h2 : (2:Int)^125 = 42535295865117307932921825928971026432 := by norm_num
    rw [h2] at ht; linarith [he, ht]
  -- (4) (−tod)·ev = (den²−num²)/4 ; 9·num²≥4·den² ⟹ 4·(−tod)·ev = den²−num² ≤ den² − (4/9)den² = (5/9)den²
  --     ⟹ 36·(−tod)·ev ≤ 5·den².  (num=ev+tod, den=ev−tod, num²−tod... use ring)
  have hstep4 : 36 * ((-tod) * ev) ≤ 5 * (ev - tod) ^ 2 := by
    have hsq : 9 * (ev + tod) ^ 2 ≥ 4 * (ev - tod) ^ 2 := by nlinarith [h32', hnumnn, hdenpos]
    nlinarith [hsq]
  -- abstract den, od, DE; carry the chain through the positive product od·den
  set den := ev - tod with hdendef'
  have hdR2 : (r0 + 2 ^ 126) * den ≤ 2 ^ 127 * ev := hstep2
  have hr0p : (0:Int) ≤ r0 + 2 ^ 126 := by
    obtain ⟨hr0lo, _⟩ := r0Tree_bounds hx hC hC0
    have hr0nn : (0:Int) ≤ r0 := by linarith [hr0lo]
    positivity
  -- A1 := (−t)·(r0+2^126)·(od·den) ≤ 2^255·5·den²/36 ... carry without division:
  -- chain on 36·A1 ≤ 5·2^255·den²
  have hntden : (0:Int) ≤ 2 ^ 128 * (-tod) := mul_nonneg (by norm_num) (by linarith [htod_np])
  -- (−t)·od·(r0+2^126)·den ≤ 2^128·(−tod)·(r0+2^126)·den  [hstep1, (r0+2^126)·den ≥ 0]
  have hP1 : (-t) * od * ((r0 + 2 ^ 126) * den) ≤ 2 ^ 128 * (-tod) * ((r0 + 2 ^ 126) * den) := by
    apply mul_le_mul_of_nonneg_right hstep1 (mul_nonneg hr0p (le_of_lt hdenpos))
  -- 2^128·(−tod)·(r0+2^126)·den ≤ 2^128·(−tod)·2^127·ev  [hstep2, 2^128(−tod) ≥ 0]
  have hP2 : 2 ^ 128 * (-tod) * ((r0 + 2 ^ 126) * den) ≤ 2 ^ 128 * (-tod) * (2 ^ 127 * ev) :=
    mul_le_mul_of_nonneg_left hdR2 hntden
  -- combine + hstep4: 36·(−t)·od·(r0+2^126)·den ≤ 36·2^255·(−tod)·ev ≤ 5·2^255·den²
  have hevnn : (0:Int) ≤ ev := by rw [hevdef]; exact Int.natCast_nonneg _
  have hP3 : 36 * ((-t) * od * ((r0 + 2 ^ 126) * den)) ≤ 5 * 2 ^ 255 * den ^ 2 := by
    have h255 : 2 ^ 128 * (-tod) * (2 ^ 127 * ev) = 2 ^ 255 * ((-tod) * ev) := by
      rw [show (2:Int) ^ 255 = 2 ^ 128 * 2 ^ 127 from by rw [← pow_add]]; ring
    have hchain : (-t) * od * ((r0 + 2 ^ 126) * den) ≤ 2 ^ 255 * ((-tod) * ev) := by
      rw [← h255]; linarith [hP1, hP2]
    have h36 : 36 * (2 ^ 255 * ((-tod) * ev)) ≤ 2 ^ 255 * (5 * den ^ 2) := by
      have := mul_le_mul_of_nonneg_left hstep4 (by positivity : (0:Int) ≤ 2 ^ 255)
      nlinarith [this]
    nlinarith [hchain, h36, (by positivity : (0:Int) ≤ (36:Int))]
  -- DE > 2^1193·(den − 2); od ≥ B4.  RHS 64·DE·(od·den) ≥ 64·2^1193(den−2)·B4·den
  have hDElo : 2 ^ 1193 * den - 2 * 2 ^ 1193 < DE := hdenlo
  -- final: 100·W·2^1039·(−t)·(r0+2^126) ≤ 64·DE.  multiply both by od·den (>0) and use 36·(LHS·od·den) ≤ ...
  set q := od * den with hqdef
  have hqpos : (0:Int) < q := by rw [hqdef]; exact mul_pos hodpos hdenpos
  -- 36·100·W·2^1039·(−t)·(r0+2^126)·q ≤ 100·W·2^1039·(5·2^255·den²)  [hP3 scaled]
  -- and 64·DE·q ≥ 64·(2^1193 den − 2·2^1193)·B4·den  via DE>… od≥B4
  -- prove via le_of_mul_le_mul_right with multiplier q, after establishing the multiplied inequality.
  rw [← mul_le_mul_right hqpos]
  -- goal: 100·W·2^1039·(−t)·(r0+2^126)·q ≤ 64·DE·q
  have hLHS : 100 * (69402657 * 2 ^ 1039 * (-t) * (r0 + 2 ^ 126)) * q =
      100 * 69402657 * 2 ^ 1039 * ((-t) * od * ((r0 + 2 ^ 126) * den)) := by rw [hqdef]; ring
  rw [hLHS]
  -- 36·LHS ≤ 100·69402657·2^1039·(5·2^255·den²) =: RHS36 ; and 36·(64·DE·q) ≥ 36·64·(2^1193 den − 2·2^1193)·B4·den
  -- show LHS ≤ 64·DE·q via: 36·LHS ≤ 36·(64·DE·q)
  have hmul36 : 36 * (100 * 69402657 * 2 ^ 1039 * ((-t) * od * ((r0 + 2 ^ 126) * den))) ≤
      36 * (64 * DE * q) := by
    have hL : 36 * (100 * 69402657 * 2 ^ 1039 * ((-t) * od * ((r0 + 2 ^ 126) * den))) ≤
        100 * 69402657 * 2 ^ 1039 * (5 * 2 ^ 255 * den ^ 2) := by
      have := mul_le_mul_of_nonneg_left hP3 (by positivity : (0:Int) ≤ 100 * 69402657 * 2 ^ 1039)
      nlinarith [this]
    have hR : 100 * 69402657 * 2 ^ 1039 * (5 * 2 ^ 255 * den ^ 2) ≤ 36 * (64 * DE * q) := by
      -- 36·64·DE·q ≥ 36·64·(2^1193 den − 2·2^1193)·B4·den (DE > …, od ≥ B4, den > 0)
      have hDEq : 36 * (64 * DE * q) ≥ 36 * 64 * ((2 ^ 1193 * den - 2 * 2 ^ 1193) * (51893481707599524783927774179503442518 * den)) := by
        rw [hqdef]
        have hDEnn : (0:Int) ≤ DE := by
          have := denExpV_lb_neg hx hC hC0 htneg; rw [← hDEdef] at this
          have h2 : (0:Int) < 2 ^ 1317 := by positivity
          linarith [this, h2]
        have h1 : (2 ^ 1193 * den - 2 * 2 ^ 1193) * 51893481707599524783927774179503442518 ≤ DE * od :=
          mul_le_mul (le_of_lt hDElo) hodB4 (by norm_num) hDEnn
        nlinarith [h1, hdenpos]
      -- 100·69402657·5·2^1294·den² ≤ 36·64·2^1193·B4·(den−2)·den   (factor 2^1193, den)
      have hcore : 100 * 69402657 * 2 ^ 1039 * (5 * 2 ^ 255 * den ^ 2) ≤
          36 * 64 * ((2 ^ 1193 * den - 2 * 2 ^ 1193) * (51893481707599524783927774179503442518 * den)) := by
        -- both sides = (·)·2^1193·den.  LHS = (100·69402657·5·2^101)·2^1193·den².
        have hpe1 : (2:Int) ^ 1039 * 2 ^ 255 = 2 ^ 101 * 2 ^ 1193 := by rw [← pow_add, ← pow_add]
        have eL : 100 * 69402657 * 2 ^ 1039 * (5 * 2 ^ 255 * den ^ 2) =
            (100 * 69402657 * 5 * 2 ^ 101) * (2 ^ 1193 * den ^ 2) := by
          linear_combination (100 * 69402657 * 5 * den ^ 2) * hpe1
        have eR : 36 * 64 * ((2 ^ 1193 * den - 2 * 2 ^ 1193) * (51893481707599524783927774179503442518 * den)) =
            (36 * 64 * 51893481707599524783927774179503442518) * (2 ^ 1193 * (den - 2) * den) := by ring
        rw [eL, eR]
        -- (100·69402657·5·2^101)·den ≤ (36·64·B4)·(den−2)  [divide common 2^1193·den; den ≥ 0.72·2^126 ≫ 2]
        have hfactor : (100 * 69402657 * 5 * 2 ^ 101 : Int) * den ≤ (36 * 64 * 51893481707599524783927774179503442518) * (den - 2) := by
          nlinarith [hden072, hdenpos]
        have hp1193den : (0:Int) ≤ 2 ^ 1193 * den := by positivity
        nlinarith [hfactor, hp1193den, hdenpos, (by positivity : (0:Int) ≤ (2:Int)^1193)]
      linarith [hDEq, hcore]
    linarith [hL, hR]
  nlinarith [hmul36]

theorem r0_real_over_tight_neg {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh)
    (htneg : int256 (tTree x) ≤ 0) :
    (int256 (r0Tree x) : Real) ≤ (2 ^ 126 : Real) * Real.exp (reducedArg x) + 19 / 25 := by
  have htdom := tdom_neg hx hC hC0 htneg
  set t := int256 (tTree x) with htdef
  have hDElb := denExpV_lb_neg hx hC hC0 htneg
  set NE := evalPoly ExpCertV.numExpV t with hNEdef
  set DE := evalPoly ExpCertV.denExpV t with hDEdef
  have hDEpos_int : (0 : Int) < DE := by
    have : (0:Int) < 2 ^ 1317 := by positivity
    linarith [hDElb, this]
  have hDEpos : (0 : Real) < (DE : Real) := by exact_mod_cast hDEpos_int
  obtain ⟨hNEpos, _⟩ := certNE_pos_neg_aux htneg htdom
  have hNEnn : (0 : Real) ≤ (NE : Real) := by have : (0:Int) ≤ NE := le_of_lt hNEpos
                                              exact_mod_cast this
  set r0 := int256 (r0Tree x) with hr0def
  -- certLo_real_neg: NE/DE ≤ Et·Mpp, Mpp = (2^130+1)/2^130
  set Et := Real.exp ((t : Real) / (2 ^ 128 : Real)) with hEtdef
  have hcertlo := certLo_real_neg htneg htdom
  set Mpp : Real := (2 ^ 130 + 1 : Real) / (2 ^ 130 : Real) with hMppdef
  have hNEDE_le : (NE : Real) / (DE : Real) ≤ Et * Mpp := by
    have hc : ((2 ^ 130 : Int) : Real) * (NE : Real) /
        (((2 ^ 130 + 1 : Int) : Real) * (DE : Real)) ≤ Et := hcertlo
    rw [hMppdef]
    have key : (NE : Real) / (DE : Real) =
        ((2 ^ 130 + 1 : Real) / (2 ^ 130 : Real)) *
          (((2 ^ 130 : Int) : Real) * (NE : Real) /
            (((2 ^ 130 + 1 : Int) : Real) * (DE : Real))) := by
      push_cast; field_simp; ring
    rw [key, mul_comm Et _]; exact mul_le_mul_of_nonneg_left hc (by positivity)
  -- Et ≤ 1 (t ≤ 0)
  have hEt_le_one : Et ≤ 1 := by
    rw [hEtdef, show (1:Real) = Real.exp 0 from (Real.exp_zero).symm]
    apply Real.exp_le_exp.mpr
    have htR : (t : Real) ≤ 0 := by have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr htneg; push_cast at this; linarith [this]
    apply div_nonpos_of_nonpos_of_nonneg htR (by positivity)
  have hEtnn : (0:Real) ≤ Et := le_of_lt (Real.exp_pos _)
  -- cR_neg: r0·DE − 2^126·NE ≤ (64/100)·DE  (Int: certRatio_neg ≤ W·2^1039(−t)(r0+2^126), bound by 64·DE/100)
  have hcR' : (r0 : Real) * (DE : Real) - (2 ^ 126 : Real) * (NE : Real) ≤ (64 / 100) * (DE : Real) := by
    have hcr := r0_certRatio_over_neg hx hC hC0 htneg
    have hbd := r0_certRatio_over_neg_bound hx hC hC0 htneg
    -- chain (Int): 100·(r0·DE − 2^126·NE) ≤ 100·W·2^1039·(−t)·(r0+2^126) ≤ 64·DE
    have hint : 100 * (r0 * (evalPoly ExpCertV.denExpV t) - 2 ^ 126 * (evalPoly ExpCertV.numExpV t)) ≤
        64 * (evalPoly ExpCertV.denExpV t) := by
      have h1 : 100 * (r0 * (evalPoly ExpCertV.denExpV t) - 2 ^ 126 * (evalPoly ExpCertV.numExpV t)) ≤
          100 * (69402657 * 2 ^ 1039 * (-t) * (r0 + 2 ^ 126)) := by
        apply mul_le_mul_of_nonneg_left hcr (by norm_num)
      linarith [h1, hbd]
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr hint; push_cast at this
    rw [hNEdef, hDEdef]; linarith [this]
  -- r0 ≤ 2^126·NE/DE + 64/100
  have hr0_div : (r0 : Real) ≤ (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) + 64 / 100 := by
    have hkey : (r0 : Real) ≤ ((2 ^ 126 : Real) * (NE : Real) + (64 / 100) * (DE : Real)) / (DE : Real) := by
      rw [le_div_iff₀ hDEpos]; nlinarith [hcR', hDEpos]
    rw [add_div, mul_div_assoc, mul_div_assoc, div_self (ne_of_gt hDEpos), mul_one] at hkey
    linarith [hkey]
  -- assemble: r0 ≤ 2^126·Et·Mpp + 64/100 = 2^126·Et + 2^126·Et·(Mpp−1) + 64/100
  --   ≤ 2^126·Et + 1/16 + 64/100; 2^126·Et ≤ 2^126·exp(rt) + 1/128 (gap1 over)
  have hMpp1 : Mpp - 1 = 1 / (2 ^ 130 : Real) := by rw [hMppdef]; field_simp
  have hcMp : (2 ^ 126 : Real) * Et * (Mpp - 1) ≤ 1 / 16 := by
    rw [hMpp1]
    have : (2 ^ 126 : Real) * Et * (1 / (2 ^ 130 : Real)) ≤ (2 ^ 126 : Real) * 1 * (1 / (2 ^ 130 : Real)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hEt_le_one (by positivity)
    have hn : (2 ^ 126 : Real) * 1 * (1 / (2 ^ 130 : Real)) ≤ 1 / 16 := by norm_num
    linarith [this, hn]
  set Ert := Real.exp (reducedArg x) with hErtdef
  have hgapover := reducedArg_close_over hx hC hC0
  have hExp_diff : Et - Ert ≤ ((t : Real) / (2 ^ 128 : Real) - reducedArg x) * Et := exp_diff_le _ _
  have hcGap1 : (2 ^ 126 : Real) * (Et - Ert) ≤ 1 / 128 := by
    have h1 : Et - Ert ≤ (1 / (32 * (2 ^ 128 : Real))) * Et :=
      le_trans hExp_diff (mul_le_mul_of_nonneg_right (le_of_lt hgapover) hEtnn)
    have h2 : (2 ^ 126 : Real) * (Et - Ert) ≤ (2 ^ 126 : Real) * ((1 / (32 * (2 ^ 128 : Real))) * Et) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (2 ^ 126 : Real) * ((1 / (32 * (2 ^ 128 : Real))) * Et) ≤
        (2 ^ 126 : Real) * ((1 / (32 * (2 ^ 128 : Real))) * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEt_le_one (by positivity)) (by positivity)
    have h4 : (2 ^ 126 : Real) * ((1 / (32 * (2 ^ 128 : Real))) * 1) ≤ 1 / 128 := by norm_num
    linarith [h2, h3, h4]
  have hNEMp : (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) ≤
      (2 ^ 126 : Real) * Et + (2 ^ 126 : Real) * Et * (Mpp - 1) := by
    have h := mul_le_mul_of_nonneg_left hNEDE_le (by positivity : (0:Real) ≤ (2 ^ 126 : Real))
    nlinarith [h]
  have hEtErt : (2 ^ 126 : Real) * Et ≤ (2 ^ 126 : Real) * Ert + 1 / 128 := by nlinarith [hcGap1]
  calc (r0 : Real) ≤ (2 ^ 126 : Real) * ((NE : Real) / (DE : Real)) + 64 / 100 := hr0_div
    _ ≤ ((2 ^ 126 : Real) * Et + (2 ^ 126 : Real) * Et * (Mpp - 1)) + 64 / 100 := by linarith [hNEMp]
    _ ≤ ((2 ^ 126 : Real) * Et + 1 / 16) + 64 / 100 := by linarith [hcMp]
    _ ≤ (((2 ^ 126 : Real) * Ert + 1 / 128) + 1 / 16) + 64 / 100 := by linarith [hEtErt]
    _ ≤ (2 ^ 126 : Real) * Real.exp (reducedArg x) + 19 / 25 := by
        rw [hErtdef]; have : (1:Real)/128 + 1/16 + 64/100 ≤ 19/25 := by norm_num
        linarith [this]

/-- **Per-point never-over (tight, any sign):** `r0 ≤ 2¹²⁶·exp(rt) + 19/25` (≤ MARGIN/WAD). -/
theorem r0_real_over_within {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (int256 (r0Tree x) : Real) ≤ (2 ^ 126 : Real) * Real.exp (reducedArg x) + 19 / 25 := by
  rcases le_or_gt 0 (int256 (tTree x)) with htnn | htneg
  · exact r0_real_over_tight hx hC hC0 htnn
  · exact r0_real_over_tight_neg hx hC hC0 (le_of_lt htneg)


/-! ## The octave-seam `r0`-doubling consequence -/

/-- The reduced argument is above `−log 2` on the region, so `exp(rt) > 1/2`. -/
theorem exp_reducedArg_gt_half {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (1 : Real) / 2 < Real.exp (reducedArg x) := by
  obtain ⟨htlo, _⟩ := tTree_in_cert_domain hx hC hC0
  have hclose := abs_lt.mp (reducedArg_close hx hC hC0)
  have hp128 : (0 : Real) < (2 ^ 128 : Real) := by positivity
  have htR : -(117932881612756647068972071382077242199 : Real) ≤ (int256 (tTree x) : Real) := by
    have := (@Int.cast_le Real _ _ _ _ _ _ _).mpr htlo; push_cast at this; linarith [this]
  -- rt > t/2^128 - 9/(8·2^128) ≥ -H128/2^128 - 1 > -log 2 (log2 ≥ 0.693)
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

/-- A lower bound on the quotient: `2¹²⁴ < r0Tree x`. (`r0 ≥ 2¹²⁶·exp(rt) − 705 > 2¹²⁶·(1/2) − 705`.) -/
theorem r0Tree_gt_2_124 {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (2 : Real) ^ 124 < (int256 (r0Tree x) : Real) := by
  have hu := r0_real_under hx hC hC0
  have hh := exp_reducedArg_gt_half hx hC hC0
  -- 2^126·exp(rt) > 2^126·(1/2) = 2^125; r0 ≥ 2^126·exp(rt) − 705 > 2^125 − 705 > 2^124
  have h1 : (2 ^ 126 : Real) * (1 / 2) < (2 ^ 126 : Real) * Real.exp (reducedArg x) :=
    mul_lt_mul_of_pos_left hh (by positivity)
  have h2 : (2 ^ 126 : Real) * (1 / 2) = (2 ^ 125 : Real) := by norm_num
  have h3 : (2 : Real) ^ 124 + 705 < (2 ^ 125 : Real) := by norm_num
  linarith [hu, h1, h2 ▸ h1, h3]

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

/-- **`r0` at most doubles across a seam** (real reduction of `SeamR0Bound`). The strict slack from
`exp(−1/RAY) < 1` (and `r0Tree x2 > 2¹²⁴`) dwarfs the loose per-point envelope constants. -/
theorem r0_seam_double {x1 x2 : Nat}
    (hx1 : x1 < 2 ^ 256) (hx2 : x2 < 2 ^ 256)
    (hC1 : int256 Cmask < int256 x1) (hC01 : int256 x1 < int256 C0thresh)
    (hC2 : int256 Cmask < int256 x2) (hC02 : int256 x2 < int256 C0thresh)
    (hk : int256 (kTree x2) = int256 (kTree x1) + 1)
    (hadj : int256 x2 = int256 x1 + 1) :
    int256 (r0Tree x1) < 2 * int256 (r0Tree x2) := by
  have hover1 := r0_real_over hx1 hC1 hC01
  have hunder2 := r0_real_under hx2 hC2 hC02
  have hr0_2_big := r0Tree_gt_2_124 hx2 hC2 hC02
  have hseam := reducedArg_seam hk hadj
  -- exp(-1/RAY) < 1 and ≥ 1 - 1/RAY  ⇒ 1 - exp(-1/RAY) ≥ 1/RAY - ... use the convexity-style bound
  set E1 := Real.exp (reducedArg x1) with hE1
  set E2 := Real.exp (reducedArg x2) with hE2
  set y := Real.exp (-(1 / (10 ^ 27 : Real))) with hy
  have hy_lt_one : y < 1 := by
    rw [hy]; rw [show (1:Real) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_lt_exp.mpr (by norm_num)
  have hy_pos : 0 < y := Real.exp_pos _
  -- y ≤ 1 - 1/(2·RAY)  (since exp(-z) ≤ 1 - z + z²/2 ≤ 1 - z/2 for small z>0)
  have hy_bound : y ≤ 1 - 1 / (2 * (10 ^ 27 : Real)) := by
    -- exp(-z) = 1/exp(z) ≤ 1/(1+z) ≤ 1 - z/2 for z ∈ (0,1]
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
  -- 2^126·E1 = 2·(2^126·E2)·y ≤ 2·(r0_2 + 705)·y
  have hE2bound : (2 ^ 126 : Real) * E2 ≤ (int256 (r0Tree x2) : Real) + 705 := hunder2
  have hr0_1 : (int256 (r0Tree x1) : Real) ≤ 2 * ((int256 (r0Tree x2) : Real) + 705) * y + 152 := by
    have h1 : (2 ^ 126 : Real) * E1 = 2 * ((2 ^ 126 : Real) * E2) * y := by rw [hseam]; ring
    have h2 : (int256 (r0Tree x1) : Real) ≤ (2 ^ 126 : Real) * E1 + 152 := hover1
    rw [h1] at h2
    have h3 : 2 * ((2 ^ 126 : Real) * E2) * y ≤ 2 * ((int256 (r0Tree x2) : Real) + 705) * y :=
      mul_le_mul_of_nonneg_right (by linarith [mul_le_mul_of_nonneg_left hE2bound (by norm_num : (0:Real) ≤ 2)]) (le_of_lt hy_pos)
    linarith [h2, h3]
  have hr0_2nn : (0:Real) ≤ (int256 (r0Tree x2) : Real) := by linarith [hr0_2_big, (by positivity : (0:Real) ≤ (2:Real)^124)]
  have hkey : 2 * ((int256 (r0Tree x2) : Real) + 705) * y + 152 < 2 * (int256 (r0Tree x2) : Real) := by
    -- The seam gap is dominated by `(r0 + 705) / RAY`; the quotient is above `1562` on this region.
    have hyb : 2 * ((int256 (r0Tree x2) : Real) + 705) * y ≤
        2 * ((int256 (r0Tree x2) : Real) + 705) * (1 - 1 / (2 * (10 ^ 27 : Real))) :=
      mul_le_mul_of_nonneg_left hy_bound (by linarith [hr0_2nn])
    have hexpand : 2 * ((int256 (r0Tree x2) : Real) + 705) * (1 - 1 / (2 * (10 ^ 27 : Real))) =
        2 * (int256 (r0Tree x2) : Real) + 1410 -
          ((int256 (r0Tree x2) : Real) + 705) / (10 ^ 27 : Real) := by field_simp; ring
    have hbig : ((int256 (r0Tree x2) : Real) + 705) / (10 ^ 27 : Real) > 1562 := by
      rw [gt_iff_lt, lt_div_iff₀ (by positivity)]
      nlinarith [hr0_2_big, (by norm_num : (1562:Real) * 10 ^ 27 + 1 < 2 ^ 124)]
    linarith [hyb, hexpand ▸ hyb, hbig]
  have hreal : (int256 (r0Tree x1) : Real) < 2 * (int256 (r0Tree x2) : Real) := by
    linarith [hr0_1, hkey]
  have : (int256 (r0Tree x1) : Real) < ((2 * int256 (r0Tree x2) : Int) : Real) := by
    push_cast; linarith [hreal]
  exact_mod_cast this

end ExpYul
