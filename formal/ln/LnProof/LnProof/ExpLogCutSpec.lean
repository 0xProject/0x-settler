import LnProof.FloorSpec

/-!
# Exponential/logarithm cut specification

This module makes the semantic target of the floor proof explicit without
importing `Real` or Mathlib.  The target is an arithmetized cut specification:
`CutExpLe p q y w` and `CutRatioLeExp y w p q` are the two rational
comparisons exposed by `ExpSum.capUB`/`ExpSum.capLB`, and the logarithm
predicates below define log comparisons as inverse exponential-cut
comparisons.

No theorem in this file mentions a real-valued `exp` or `log`; proving
equivalence with those functions is a separate real-analysis bridge.  The
theorems here show that the existing floor specifications are exactly these
cut-log predicates.
-/

namespace LnFloorCert

open LnGeneratedModel LnExp LnFloor

/-- Cut statement for `exp(p/q) <= y/w`: every exact Taylor partial sum is
bounded by the target rational. -/
def CutExpLe (p q y w : Nat) : Prop := capUB p q y w

/-- Cut statement for `y/w <= exp(p/q)`: one exact Taylor partial sum reaches
the target rational. -/
def CutRatioLeExp (y w p q : Nat) : Prop := capLB p q y w

/-- Cut-log lower-bound comparison for the wad input at ray scale.

`CutLeLogWadRay r x` is the real-free counterpart of
`r <= 10^27 * log(x / 10^18)`.  For negative `r`, the comparison is encoded
through the reciprocal exponential inequality. -/
def CutLeLogWadRay (r : Int) (x : Nat) : Prop :=
  if 0 <= r then
    CutExpLe (r.toNat * 2 ^ 99) QS x (10 ^ 18)
  else
    CutRatioLeExp (10 ^ 18) x ((-r).toNat * 2 ^ 99) QS

/-- Cut-log strict upper-bound comparison for the wad input at ray scale.

`CutLogWadRayLtWithMargin x b` is the real-free counterpart of
`10^27 * log(x / 10^18) < b`.  The positive-exponent branch proves a lower
cut against `(x / 10^18) / (1 - 10^-30)`, while the reciprocal branch proves
an upper cut against `(10^18 / x) * (1 - 10^-30)`.  This strictness margin
turns the non-strict cut inequalities into a strict logarithm comparison
under the external real-analysis interpretation. -/
def CutLogWadRayLtWithMargin (x : Nat) (b : Int) : Prop :=
  if 1 <= b then
    CutRatioLeExp (x * 10 ^ 31) (10 ^ 18 * (10 ^ 31 - 10)) (b.toNat * 2 ^ 99) QS
  else
    CutExpLe ((-b).toNat * 2 ^ 99) QS (10 ^ 18 * (10 ^ 31 - 10)) (x * 10 ^ 31)

/-- The complete ray-scale cut-log floor bracket. -/
def CutLnWadRayBracket (r : Int) (x : Nat) : Prop :=
  CutLeLogWadRay r x ∧ CutLogWadRayLtWithMargin x (r + 2)

/-- The wad-scale wrapper spec: a ray-scale cut-log bracket plus exact signed
floor division by `10^9`. -/
def CutLnWadSpec (ray wad : Int) (x : Nat) : Prop :=
  CutLnWadRayBracket ray x ∧ wad * 1000000000 <= ray ∧ ray < (wad + 1) * 1000000000

/-- `FloorSpecA` is exactly the lower cut-log comparison. -/
theorem FloorSpecA_iff_cutLeLogWadRay {r : Int} {x : Nat} :
    FloorSpecA r x ↔ CutLeLogWadRay r x := by
  unfold FloorSpecA CutLeLogWadRay CutExpLe CutRatioLeExp
  by_cases hr : 0 <= r <;> simp [hr]

/-- `FloorSpecB` is exactly the strict-margin upper cut-log comparison. -/
theorem FloorSpecB_iff_cutLogWadRayLtWithMargin {r : Int} {x : Nat} :
    FloorSpecB r x ↔ CutLogWadRayLtWithMargin x (r + 2) := by
  unfold FloorSpecB CutLogWadRayLtWithMargin CutExpLe CutRatioLeExp
  by_cases hr : -1 <= r
  · have hb : 1 <= r + 2 := by omega
    simp [hr, hb]
  · have hb : ¬1 <= r + 2 := by omega
    simp [hr, hb]

/-- The paired floor specification is exactly the ray-scale cut-log bracket. -/
theorem FloorSpec_iff_cutLnWadRayBracket {r : Int} {x : Nat} :
    FloorSpecA r x ∧ FloorSpecB r x ↔ CutLnWadRayBracket r x := by
  unfold CutLnWadRayBracket
  rw [FloorSpecA_iff_cutLeLogWadRay, FloorSpecB_iff_cutLogWadRayLtWithMargin]

/-- The wad wrapper floor specification is exactly the wad-scale cut spec. -/
theorem FloorSpecToWad_iff_cutLnWadSpec {ray wad : Int} {x : Nat} :
    FloorSpecToWad ray wad x ↔ CutLnWadSpec ray wad x := by
  unfold FloorSpecToWad CutLnWadSpec
  constructor
  · intro h
    obtain ⟨ha, hb, hlo, hhi⟩ := h
    exact ⟨FloorSpec_iff_cutLnWadRayBracket.mp ⟨ha, hb⟩, hlo, hhi⟩
  · intro h
    obtain ⟨hbr, hlo, hhi⟩ := h
    obtain ⟨ha, hb⟩ := FloorSpec_iff_cutLnWadRayBracket.mpr hbr
    exact ⟨ha, hb, hlo, hhi⟩

/-- The ray-scale model satisfies the explicit cut-log bracket. -/
theorem model_ln_wad_cut_spec {x : Nat} (h1 : 1 <= x) (h2 : x < 2 ^ 255) :
    CutLnWadRayBracket (toInt (model_ln_wad_evm x)) x := by
  exact FloorSpec_iff_cutLnWadRayBracket.mp (model_ln_wad_floor h1 h2)

/-- The wad-scale wrapper model satisfies the explicit cut-log wrapper spec. -/
theorem model_ln_wad_to_wad_cut_spec {x : Nat} (h1 : 1 <= x) (h2 : x < 2 ^ 255) :
    CutLnWadSpec (toInt (model_ln_wad_evm x)) (toInt (model_ln_wad_to_wad_evm x)) x := by
  exact FloorSpecToWad_iff_cutLnWadSpec.mp (model_ln_wad_to_wad_floor h1 h2)

end LnFloorCert
