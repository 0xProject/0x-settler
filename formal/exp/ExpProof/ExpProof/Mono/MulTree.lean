import ExpProof.Mono.Tree

/-!
# `mulExpRay` runtime normal form

The dynamic-scale entrypoint shares the exponent kernel with `expRayToWad`. This file names the
extra word computations around that kernel: absolute-value/sign extraction, scale-headroom
selection, the dynamic closing shift, the panic-guard word, and the closing `sgn(y)` multiply
that both reapplies the sign and collapses the zero multiplier.
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

/-- Dynamic closing shift `S - k`, shared by the guard and the kernel call. -/
def mulShiftTree (y x : Nat) : Nat :=
  evmSub (scaleShiftTree (absTree y)) (kTree x)

/-- The branch word for the `Panic(17)` guard. -/
def mulExpGuardTree (y x : Nat) : Nat :=
  let outOfRange := evmOr (evmGt (absTree y) scaleQ67) (evmIszero (evmSlt x mulExpRayHi))
  let inaccurate :=
    evmAnd (evmAnd (evmIszero (evmEq x 0)) (evmSgt x mulExpRayZeroMax))
      (evmSlt (mulShiftTree y x) 2)
  evmOr outOfRange inaccurate

/-- The dynamic-scaled quotient before the closing shift. -/
def r0MulTree (y x : Nat) : Nat :=
  evmDiv (evmMul (mulScaleTree y) (evmAdd (evTree x) (todTree x)))
    (evmSub (evTree x) (todTree x))

theorem r0MulTree_eq_scaled (y x : Nat) : r0MulTree y x = r0ScaledTree (mulScaleTree y) x := rfl

/-- The nonnegative magnitude returned by the shared kernel before the `sgn(y)` multiply. -/
def mulMagnitudeTree (y x : Nat) : Nat :=
  evmAdd (evmIszero x)
    (evmMul (evmSlt mulExpRayZeroMax x)
      (evmShr (mulShiftTree y x) (evmSub (r0MulTree y x) marginWord)))

/-- `sgn(y)` as a word: the sign mask (`-1`) for negative inputs, `1` for positive inputs, and
`0` for a zero multiplier. -/
def sgnTree (y : Nat) : Nat :=
  evmOr (signTree y) (evmLt 0 (absTree y))

/-- The result word: the kernel magnitude times `sgn(y)`, which reapplies the sign and zeroes
the (unspecified) magnitude of a zero multiplier in one step. -/
def mulExpTree (y x : Nat) : Nat :=
  evmMul (mulMagnitudeTree y x) (sgnTree y)

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
  exact FormalYul.Preservation.evmMul_lt_pow256 _ _

theorem sgnTree_zero : sgnTree 0 = 0 := by
  simp [sgnTree, signTree, absTree, Common.Word.evmXor, evmSar, evmSub, evmLt, evmOr,
    u256, WORD_MOD]

/-- A zero multiplier's result word is zero: `sgn(0) = 0` collapses the kernel output. -/
theorem mulExpTree_zero (x : Nat) : mulExpTree 0 x = 0 := by
  unfold mulExpTree
  rw [sgnTree_zero]
  simp [evmMul, u256, WORD_MOD]

end ExpYul
