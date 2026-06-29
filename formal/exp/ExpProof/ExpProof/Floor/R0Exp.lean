import ExpProof.Floor.R0Bound
import ExpProof.Floor.CapsV
import ExpProof.Floor.Reduce
import ExpProof.Mono.Quot
import Common.Seam.RealExpBridge

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

/-- One `v`-step of the even Horner polynomial is below `2⁵⁵³` for `v < 2¹²⁶`. -/
theorem evNumV_step {v : Nat} (hv : v < 2 ^ 126) :
    (evNumV (v + 1) : Int) - (evNumV v : Int) < 2 ^ 553 := by
  unfold evNumV
  push_cast
  have hvle : (v : Int) < 2 ^ 126 := by exact_mod_cast hv
  have hvnn : (0 : Int) ≤ (v : Int) := by positivity
  nlinarith [hvle, hvnn, mul_nonneg hvnn hvnn, Int.mul_nonneg hvnn (Int.mul_nonneg hvnn hvnn),
    Int.mul_nonneg (Int.mul_nonneg hvnn hvnn) (Int.mul_nonneg hvnn hvnn)]

/-- One `v`-step of the odd Horner polynomial is below `2⁵³⁰` for `v < 2¹²⁶`. -/
theorem odNumV_step {v : Nat} (hv : v < 2 ^ 126) :
    (odNumV (v + 1) : Int) - (odNumV v : Int) < 2 ^ 530 := by
  unfold odNumV
  push_cast
  have hvle : (v : Int) < 2 ^ 126 := by exact_mod_cast hv
  have hvnn : (0 : Int) ≤ (v : Int) := by positivity
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
`2¹¹⁹³·evTree x ≤ evalPoly evNumVPoly t < 2¹¹⁹³·evTree x + 3·2¹¹⁹³`. -/
theorem evNumVPoly_bracket {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    2 ^ 1193 * (evTree x : Int) ≤ evalPoly ExpCertV.evNumVPoly (int256 (tTree x)) ∧
      evalPoly ExpCertV.evNumVPoly (int256 (tTree x)) < 2 ^ 1193 * (evTree x : Int) + 3 * 2 ^ 1193 := by
  obtain ⟨_, hvlt⟩ := vTree_eq hx hC hC0
  obtain ⟨hg2lo, hg2hi⟩ := evTree_bracket hvlt
  obtain ⟨hsqlo, hsqhi⟩ := tsq_split hx hC hC0
  set t := int256 (tTree x) with htdef
  have hsqnn : (0 : Int) ≤ t ^ 2 := sq_nonneg _
  have hgridnn : (0 : Int) ≤ 2 ^ 128 * (vTree x : Int) := by positivity
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
  have hg2hi' : (evNumV (vTree x) : Int) * 2 ^ 640 < 2 ^ 1193 * (evTree x : Int) + 2 * 2 ^ 1193 := by
    have h : evNumV (vTree x) < 2 ^ 553 * evTree x + 2 * 2 ^ 553 := hg2hi
    have : (evNumV (vTree x) : Int) < (2 ^ 553 * evTree x + 2 * 2 ^ 553 : Nat) := by exact_mod_cast h
    push_cast at this; nlinarith [this]
  -- step bound: evNumV(vTree+1)·2^640 < evNumV(vTree)·2^640 + 2^1193
  have hstep := evNumV_step hvlt
  have hstep' : (evNumV (vTree x + 1) : Int) * 2 ^ 640 < (evNumV (vTree x) : Int) * 2 ^ 640 + 2 ^ 1193 := by
    nlinarith [hstep]
  refine ⟨le_trans hg2lo' hmono_lo, ?_⟩
  calc evalPoly Pev (t ^ 2) ≤ (evNumV (vTree x + 1) : Int) * 2 ^ 640 := hmono_hi
    _ < (evNumV (vTree x) : Int) * 2 ^ 640 + 2 ^ 1193 := hstep'
    _ < 2 ^ 1193 * (evTree x : Int) + 2 * 2 ^ 1193 + 2 ^ 1193 := by linarith [hg2hi']
    _ = 2 ^ 1193 * (evTree x : Int) + 3 * 2 ^ 1193 := by ring

end ExpYul
