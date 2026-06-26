import LnProof.Floor.Spec
import LnProof.Spec.Cut

open FormalYul
open FormalYul.Preservation

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

open LnYul LnExp LnFloor

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

/-- The ray-scale body satisfies the explicit cut-log bracket. -/
theorem lnWadToRayBody_cut_spec {x : Nat} (h1 : 1 <= x) (h2 : x < 2 ^ 255) :
    CutLnWadRayBracket (int256 (lnWadToRayBody x)) x := by
  exact FloorSpec_iff_cutLnWadRayBracket.mp (lnWadToRayBody_floor h1 h2)

/-- The wad-scale wrapper body satisfies the explicit cut-log wrapper spec. -/
theorem lnWadBody_cut_spec {x : Nat} (h1 : 1 <= x) (h2 : x < 2 ^ 255) :
    CutLnWadSpec (int256 (lnWadToRayBody x)) (int256 (lnWadBody x)) x := by
  exact FloorSpecToWad_iff_cutLnWadSpec.mp (lnWadBody_floor h1 h2)

end LnFloorCert
