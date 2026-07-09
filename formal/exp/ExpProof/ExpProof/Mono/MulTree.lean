import ExpProof.Mono.Tree

/-!
# `mulExpRay` runtime normal form

The dynamic-scale entrypoint shares the exponent kernel with `expRayToWad`. This file names the
extra word computations around that kernel: absolute-value/sign extraction, scale shift selection,
dynamic closing shift, and sign reapplication.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation
open Common.Word

set_option maxRecDepth 100000

/-- The sign mask produced by `sar(255, y)`: `0` for nonnegative inputs and `-1` as a word for
negative inputs. -/
def signTree (y : Nat) : Nat :=
  evmSar 0xff y

/-- Absolute value as a word, computed without negating `int256.min`. -/
def absTree (y : Nat) : Nat :=
  evmSub (evmXor y (signTree y)) (signTree y)

/-- The largest shift chosen by the compiled bit-length estimate, corrected by one if the shifted
magnitude exceeds `scaleQ67`. -/
def scaleShiftTree (ay : Nat) : Nat :=
  let s := evmSub (evmClz ay) scaleMaxClz
  evmSub s (evmGt (evmShl s ay) scaleQ67)

/-- Dynamic pre-shift scale `abs(y) << S`. -/
def mulScaleTree (y : Nat) : Nat :=
  evmShl (scaleShiftTree (absTree y)) (absTree y)

/-- Dynamic closing shift `S - k`. -/
def mulShiftTree (y x : Nat) : Nat :=
  evmSub (scaleShiftTree (absTree y)) (kTree x)

/-- The branch word for the `Panic(17)` guard. -/
def mulExpGuardTree (y x : Nat) : Nat :=
  let ay := absTree y
  let s := scaleShiftTree ay
  let k := kTree x
  let outOfRange := evmOr (evmGt ay scaleQ67) (evmIszero (evmSlt x xHiMulExpRay))
  let inaccurate :=
    evmAnd (evmAnd (evmIszero (evmEq x 0)) (evmSgt x xLoZeroMulExpRay))
      (evmSgt k (evmSub s 2))
  evmOr outOfRange inaccurate

/-- The dynamic-scaled quotient before the closing shift. -/
def r0MulTree (y x : Nat) : Nat :=
  evmDiv (evmMul (mulScaleTree y) (evmAdd (evTree x) (todTree x)))
    (evmSub (evTree x) (todTree x))

/-- The nonnegative magnitude returned by the shared kernel before the sign mask is applied. -/
def mulMagnitudeTree (y x : Nat) : Nat :=
  evmAdd (evmIszero x)
    (evmMul (evmSlt xLoZeroMulExpRay x)
      (evmShr (mulShiftTree y x) (evmSub (r0MulTree y x) marginWord)))

/-- Signed result word after applying `y`'s sign mask. -/
def mulExpTree (y x : Nat) : Nat :=
  let m := mulMagnitudeTree y x
  evmSub (evmXor m (signTree y)) (signTree y)

theorem absTree_lt (y : Nat) : absTree y < 2 ^ 256 := by
  unfold absTree
  exact evmSub_lt _ _

theorem scaleShiftTree_lt (ay : Nat) : scaleShiftTree ay < 2 ^ 256 := by
  unfold scaleShiftTree
  exact evmSub_lt _ _

theorem mulScaleTree_lt (y : Nat) : mulScaleTree y < 2 ^ 256 := by
  unfold mulScaleTree
  exact evmShl_lt _ _

theorem mulShiftTree_lt (y x : Nat) : mulShiftTree y x < 2 ^ 256 := by
  unfold mulShiftTree
  exact evmSub_lt _ _

theorem mulExpGuardTree_lt (y x : Nat) : mulExpGuardTree y x < 2 ^ 256 := by
  unfold mulExpGuardTree
  simpa [WORD_MOD] using evmOr_lt_WORD_MOD _ _

theorem r0MulTree_lt (y x : Nat) : r0MulTree y x < 2 ^ 256 := by
  unfold r0MulTree
  exact evmDiv_lt _ _

theorem mulMagnitudeTree_lt (y x : Nat) : mulMagnitudeTree y x < 2 ^ 256 := by
  unfold mulMagnitudeTree
  exact evmAdd_lt _ _

theorem mulExpTree_lt (y x : Nat) : mulExpTree y x < 2 ^ 256 := by
  unfold mulExpTree
  exact evmSub_lt _ _

end ExpYul
