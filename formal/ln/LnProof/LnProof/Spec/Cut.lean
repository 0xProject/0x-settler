import Common.Foundation.ExpSum

/-!
# Shared exponential/logarithm cut specification

Single home for the common denominator `QS` and the arithmetized cut predicates
shared by the floor proof (`ExpLogCutSpec`) and the real-analysis bridge
(`LnRealBridge`). `CutExpLe`/`CutRatioLeExp` are the two rational comparisons
exposed by `ExpSum.capUB`/`ExpSum.capLB`; the logarithm predicates define log
comparisons as inverse exponential-cut comparisons. No `Real`/Mathlib dependency.
-/

set_option maxRecDepth 8192

namespace LnFloor

/-- Common denominator of every exponent argument. -/
def QS : Nat := 10 ^ 27 * 2 ^ 99

theorem QS_pos : 0 < QS := by decide

end LnFloor

namespace LnFloorCert

open Common.Exp LnFloor

/-- Cut statement for `exp(p/q) <= y/w`: every exact Taylor partial sum is
bounded by the target rational. -/
def CutExpLe (p q y w : Nat) : Prop := capUB p q y w

/-- Cut statement for `y/w <= exp(p/q)`: one exact Taylor partial sum reaches
the target rational. -/
def CutRatioLeExp (y w p q : Nat) : Prop := capLB p q y w

/-- Cut-log lower-bound comparison for the wad input at ray scale.
`CutLeLogWadRay r x` is the real-free counterpart of `r <= 10^27 * log(x / 10^18)`.
For negative `r`, the comparison is encoded through the reciprocal exponential
inequality. -/
def CutLeLogWadRay (r : Int) (x : Nat) : Prop :=
  if 0 ≤ r then
    CutExpLe (r.toNat * 2 ^ 99) QS x (10 ^ 18)
  else
    CutRatioLeExp (10 ^ 18) x ((-r).toNat * 2 ^ 99) QS

/-- Cut-log strict upper-bound comparison for the wad input at ray scale.
`CutLogWadRayLtWithMargin x b` is the real-free counterpart of
`10^27 * log(x / 10^18) < b`. The strictness margin turns the non-strict cut
inequalities into a strict logarithm comparison under the external
real-analysis interpretation. -/
def CutLogWadRayLtWithMargin (x : Nat) (b : Int) : Prop :=
  if 1 ≤ b then
    CutRatioLeExp (x * 10 ^ 31) (10 ^ 18 * (10 ^ 31 - 10)) (b.toNat * 2 ^ 99) QS
  else
    CutExpLe ((-b).toNat * 2 ^ 99) QS (10 ^ 18 * (10 ^ 31 - 10)) (x * 10 ^ 31)

/-- The complete ray-scale cut-log floor bracket. -/
def CutLnWadRayBracket (r : Int) (x : Nat) : Prop :=
  CutLeLogWadRay r x ∧ CutLogWadRayLtWithMargin x (r + 2)

/-- The wad-scale wrapper spec: a ray-scale cut-log bracket plus exact signed
floor division by `10^9`. -/
def CutLnWadSpec (ray wad : Int) (x : Nat) : Prop :=
  CutLnWadRayBracket ray x ∧ wad * 1000000000 ≤ ray ∧ ray < (wad + 1) * 1000000000

end LnFloorCert
