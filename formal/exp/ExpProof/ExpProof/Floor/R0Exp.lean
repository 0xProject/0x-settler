import ExpProof.Floor.R0Bound
import ExpProof.Floor.CapsV
import ExpProof.Floor.Reduce
import ExpProof.Mono.Quot
import ExpProof.Mono.Cross
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

/-- **The odd cert polynomial brackets the runtime odd accumulator** (gap-2 ∘ v-truncation):
`2¹⁰⁴²·odTree x ≤ evalPoly odNumVPoly t < 2¹⁰⁴²·odTree x + 3·2¹⁰⁴²`. -/
theorem odNumVPoly_bracket {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    2 ^ 1042 * (odTree x : Int) ≤ evalPoly ExpCertV.odNumVPoly (int256 (tTree x)) ∧
      evalPoly ExpCertV.odNumVPoly (int256 (tTree x)) < 2 ^ 1042 * (odTree x : Int) + 3 * 2 ^ 1042 := by
  obtain ⟨_, hvlt⟩ := vTree_eq hx hC hC0
  obtain ⟨hg2lo, hg2hi⟩ := odTree_bracket hvlt
  obtain ⟨hsqlo, hsqhi⟩ := tsq_split hx hC hC0
  set t := int256 (tTree x) with htdef
  have hsqnn : (0 : Int) ≤ t ^ 2 := sq_nonneg _
  have hgridnn : (0 : Int) ≤ 2 ^ 128 * (vTree x : Int) := by positivity
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
  have hg2hi' : (odNumV (vTree x) : Int) * 2 ^ 512 < 2 ^ 1042 * (odTree x : Int) + 2 * 2 ^ 1042 := by
    have h : odNumV (vTree x) < 2 ^ 530 * odTree x + 2 * 2 ^ 530 := hg2hi
    have : (odNumV (vTree x) : Int) < (2 ^ 530 * odTree x + 2 * 2 ^ 530 : Nat) := by exact_mod_cast h
    push_cast at this; nlinarith [this]
  have hstep := odNumV_step hvlt
  have hstep' : (odNumV (vTree x + 1) : Int) * 2 ^ 512 < (odNumV (vTree x) : Int) * 2 ^ 512 + 2 ^ 1042 := by
    nlinarith [hstep]
  refine ⟨le_trans hg2lo' hmono_lo, ?_⟩
  calc evalPoly Pod (t ^ 2) ≤ (odNumV (vTree x + 1) : Int) * 2 ^ 512 := hmono_hi
    _ < (odNumV (vTree x) : Int) * 2 ^ 512 + 2 ^ 1042 := hstep'
    _ < 2 ^ 1042 * (odTree x : Int) + 2 * 2 ^ 1042 + 2 ^ 1042 := by linarith [hg2hi']
    _ = 2 ^ 1042 * (odTree x : Int) + 3 * 2 ^ 1042 := by ring

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
  have hodnn : (0 : Int) ≤ (odTree x : Int) := by positivity
  -- 2^128·tod ≤ t·odTree < 2^128·tod + 2^128
  -- multiply odd bracket by t·2^23 (t ≥ 0):
  have hmul_lo : t * (2 ^ 1042 * (odTree x : Int)) ≤ t * evalPoly ExpCertV.odNumVPoly t :=
    mul_le_mul_of_nonneg_left hodlo htnn
  have hmul_hi : t * evalPoly ExpCertV.odNumVPoly t ≤ t * (2 ^ 1042 * (odTree x : Int) + 3 * 2 ^ 1042) :=
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
  · -- 2^23·(t·odpoly) < 2^1193·tod + 2^5·2^1193
    -- t·odpoly ≤ t·(2^1042·odTree + 3·2^1042) = 2^1042·(t·odTree) + 3·2^1042·t
    -- t·odTree < 2^128·tod + 2^128. t < 2^128 (|t| < H128 < 2^128).
    obtain ⟨htlo', hthi'⟩ := tTree_bound hx hC hC0
    have htlt : t < 2 ^ 128 := by
      have : t < 2 ^ 127 := by rw [show ((2:Int)^127) = 170141183460469231731687303715884105728 from by norm_num]; exact hthi'
      have : (2:Int)^127 < 2 ^ 128 := by norm_num
      omega
    have key : 2 ^ 23 * (t * evalPoly ExpCertV.odNumVPoly t) <
        2 ^ 1193 * (int256 (todTree x)) + 4 * 2 ^ 1193 := by
      have h1 : t * evalPoly ExpCertV.odNumVPoly t ≤ 2 ^ 1042 * (t * (odTree x : Int)) + 3 * 2 ^ 1042 * t := by
        nlinarith [hmul_hi]
      have h2 : t * (odTree x : Int) < (2 ^ 128 : Int) * (int256 (todTree x)) + 2 ^ 128 := htod_hi
      nlinarith [h1, h2, htlt, htnn, mul_nonneg htnn hodnn]
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

end ExpYul
