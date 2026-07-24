import ExpProof.Mono.WordFacts

/-!
# Exp runtime normal form

The runtime value tree from `run_exp_ray_to_wad_evm_eq_tree` is decomposed into thin named layers so
the downstream proof can unfold one step at a time instead of materialising the full Horner tree.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word

set_option maxRecDepth 100000

/-- Octave index word `k = round(x / (10^27 * ln 2))`. -/
def kTree (x : Nat) : Nat :=
  evmSar kRoundShift (evmAdd (evmShl kHalfShift 1) (evmMul cInvQ192 x))

/-- Reduced argument `t` in Q129. -/
def tTree (x : Nat) : Nat :=
  evmSar tArgShift (evmSub (evmMul k27Q235 x) (evmMul ln2Q235 (kTree x)))

/-- `v = t^2` in Q123. -/
def vTree (x : Nat) : Nat := evmShr squareShift (evmMul (tTree x) (tTree x))

/-- `Ev(v)`, the even Horner accumulator. -/
def evTree (x : Nat) : Nat :=
  let v := vTree x
  evmAdd ev4 (evmShr evShift4 (evmMul
    (evmAdd ev3 (evmShr evShift3 (evmMul
    (evmAdd ev2 (evmShr evShift2 (evmMul
    (evmAdd ev1 (evmShr evShift1 (evmMul
    (evmAdd ev0 v) v))) v))) v))) v))

/-- `Od(v)`, the odd Horner accumulator. -/
def odTree (x : Nat) : Nat :=
  let v := vTree x
  evmAdd od4 (evmShr odShift4 (evmMul
    (evmAdd od3 (evmShr odShift3 (evmMul
    (evmAdd od2 (evmShr odShift2 (evmMul
    (evmAdd od1 (evmShr odShift1 (evmMul
    od0 v))) v))) v))) v))

/-- `t * Od(v)` in Q89. -/
def todTree (x : Nat) : Nat := evmSar todShift (evmMul (tTree x) (odTree x))

/-- The scaled rational at an explicit scale word: `⌊scale·(ev + tod)/(ev − tod)⌋`. `r0Tree` is
its `scaleQ67` instance and the `mulExpRay` quotient its dynamic-scale instance. -/
def r0ScaledTree (scale x : Nat) : Nat :=
  evmDiv (evmMul scale (evmAdd (evTree x) (todTree x))) (evmSub (evTree x) (todTree x))

/-- `10¹⁸·exp(t)` on the `2⁶⁷` output grid: the numerator is pre-scaled by `10¹⁸·2⁶⁷ = 5¹⁸·2⁸⁵`
before the single `DIV`. -/
def r0Tree (x : Nat) : Nat :=
  evmDiv (evmMul scaleQ67 (evmAdd (evTree x) (todTree x))) (evmSub (evTree x) (todTree x))

theorem r0Tree_eq_scaled (x : Nat) : r0Tree x = r0ScaledTree scaleQ67 x := rfl

/-- The floored, octave-scaled, margin-subtracted accumulator on the `2⁶⁷` output grid. -/
def r1Tree (x : Nat) : Nat :=
  evmShr (evmSub foldShift (kTree x)) (evmSub (r0Tree x) marginWord)


/-- The clamp/pin shell wrapped around `r1Tree`. -/
def expTree (x : Nat) : Nat :=
  evmAdd (evmIszero x) (evmMul (evmSlt Cmask x) (r1Tree x))

theorem r0Tree_lt (x : Nat) : r0Tree x < 2 ^ 256 := by
  unfold r0Tree
  exact evmDiv_lt _ _


theorem r1Tree_lt (x : Nat) : r1Tree x < 2 ^ 256 := by
  unfold r1Tree
  exact evmShr_lt _ _

theorem expTree_lt (x : Nat) : expTree x < 2 ^ 256 := by
  unfold expTree
  exact evmAdd_lt _ _

end ExpYul
