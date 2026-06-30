import Common.Foundation.ExpSum

/-!
# Real-free `Nat` cut specification for `expRayToWad`

The runtime reduces `x` to an octave count `k` and a reduced argument
`t ∈ [−ln2/2, ln2/2)`, then forms `exp(x/RAY) = 2^k · exp(t)`. The pre-floor
accumulator is `A = (WAD·r0 − MARGIN)/2^(126−k)` with `r0 = ê(t)·2^126` the
`sdiv` result; the runtime returns `⌊A⌋` (clamped). The correctness brackets
reduce to two rational comparisons on `exp(t)`:

* a never-over cut — an upper bound `exp(t) ≤ yUB/wUB` — that, after folding the
  octave `2^k` and subtracting the margin, gives `A ≤ E`;
* a not-too-low cut — a lower bound `yLB/wLB ≤ exp(t)` — that, after the same
  fold, gives `E < A + 1`.

These are encoded with `Common.Exp.capUB`/`capLB` over a common denominator. The
reduced argument is carried as a rational `t = tNum/tDen` and the octave as a
`Nat` exponent `k`; the negative-`x` branch is the reciprocal cut on `−t`. This
module only *defines* the cut predicates and the octave fold — it does not prove
they hold; the Taylor certificates prove that. No `Real`/Mathlib dependency.
-/

namespace ExpFloor

/-- Common denominator of the reduced exponent argument: the ray scale times the
Q99 headroom the runtime carries (mirrors the `ln` proof's `QS`). -/
def QS : Nat := 10 ^ 27 * 2 ^ 99

theorem QS_pos : 0 < QS := by
  unfold QS; exact Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))

def WAD : Nat := 10 ^ 18

theorem WAD_pos : 0 < WAD := by unfold WAD; exact Nat.pow_pos (by decide)

end ExpFloor

namespace ExpFloorCert

open Common.Exp ExpFloor

/-- Upper cut on the reduced argument: `exp(tNum/tDen) ≤ yUB/wUB`, encoded as
`Common.Exp.capUB` (every exact Taylor partial sum is bounded by the target). -/
def CutExpTaylorLe (tNum tDen yUB wUB : Nat) : Prop := capUB tNum tDen yUB wUB

/-- Lower cut on the reduced argument: `yLB/wLB ≤ exp(tNum/tDen)`, encoded as
`Common.Exp.capLB` (one exact Taylor partial sum reaches the target). -/
def CutRatioLeExpTaylor (yLB wLB tNum tDen : Nat) : Prop := capLB tNum tDen yLB wLB

/-- **Never-over cut.** The reduced-argument exponential, scaled by the octave
`2^k`, stays at or below the rational `yUB/wUB`. The Taylor certificates establish
the base `CutExpTaylorLe` (an upper cap at Taylor depth `K = 27` over the cell that
contains `tNum/tDen`); folding the octave is `capUB_pow`/`capUB_mul`. The
margin/floor step that turns `2^k·exp(t) ≤ yUB/wUB` into `A ≤ E` is a bridge
hypothesis. -/
def ExpNeverOverCut (tNum tDen k yUB wUB : Nat) : Prop :=
  capUB (k * tDen + tNum) tDen yUB wUB

/-- **Not-two-below cut.** The octave-scaled reduced exponential is at or above
the rational `yLB/wLB`. The Taylor certificate establishes the base
`CutRatioLeExpTaylor` (a lower cap at Taylor depth `K = 27`); the octave fold is
`capLB_pow`/`capLB_mul`. The margin/floor step turning `2^k·exp(t) ≥ yLB/wLB`
into `E < A + 1` is a bridge hypothesis. -/
def ExpNotTwoBelowCut (tNum tDen k yLB wLB : Nat) : Prop :=
  capLB (k * tDen + tNum) tDen yLB wLB

/-! ## Octave fold

The cut predicates are stated already-folded (`k * tDen + tNum`). The factored
form — a Taylor cap on the reduced argument plus a Taylor cap on `ln2` for the
octave factor `(e^{ln2})^k = 2^k` — composes into the folded cut via the generic
`capUB_mul`/`capUB_pow` (resp. `capLB_*`). These lemmas exhibit that composition
so the Taylor certificates can target the unfolded pieces. `ln2Num/ln2Den ≈ ln 2`. -/

/-- A reduced-argument upper cap together with an upper cap on the octave factor
`(e^{ln2Num/ln2Den})^k` (with `ln2Den = tDen`) folds into the never-over cut. -/
theorem expNeverOverCut_of_fold {tNum tDen k ln2Num yT wT yOct wOct : Nat}
    (hq : 0 < tDen)
    (hT : CutExpTaylorLe tNum tDen yT wT)
    (hOct : capUB (k * ln2Num) tDen (yOct ^ k) (wOct ^ k))
    (hln2 : ln2Num = tDen) :
    ExpNeverOverCut tNum tDen k (yT * yOct ^ k) (wT * wOct ^ k) := by
  unfold ExpNeverOverCut
  subst hln2
  rw [Nat.add_comm]
  exact capUB_mul hq hT hOct

/-- A reduced-argument lower cap together with a lower cap on the octave factor
folds into the not-two-below cut. -/
theorem expNotTwoBelowCut_of_fold {tNum tDen k ln2Num yT wT yOct wOct : Nat}
    (hT : CutRatioLeExpTaylor yT wT tNum tDen)
    (hOct : capLB (k * ln2Num) tDen (yOct ^ k) (wOct ^ k))
    (hln2 : ln2Num = tDen) :
    ExpNotTwoBelowCut tNum tDen k (yT * yOct ^ k) (wT * wOct ^ k) := by
  unfold ExpNotTwoBelowCut
  subst hln2
  rw [Nat.add_comm]
  exact capLB_mul hT hOct

end ExpFloorCert
