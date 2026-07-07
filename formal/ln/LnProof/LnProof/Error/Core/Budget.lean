import LnProof.Floor.CutEquiv
import LnProof.Error.Cert
import LnProof.Error.Core.CutDefs

/-!
# Error bound — Budget

Per-branch budget definitions (`posPhaseNatGe/Lt`, `posAvail*`, `PosShift*BudgetOk`, phase-direct predicates).
-/

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

namespace LnFloorCert

open LnYul LnFloor Common.Exp Common.Poly

attribute [local irreducible] lnWadToRayBody


def posPhaseNatGe (m c : Nat) : Nat :=
  (int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen +
    (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
      BIASc * twoPow27N * lnErrorBoundDen

def posAvailGe (m c : Nat) (r : Int) : Nat :=
  lnErrArg r - posPhaseNatGe m c

def posBaseYGe (m c : Nat) : Nat :=
  ((m * 9999999999999999999999999996615) *
    ((2 * (10 ^ 40 - 1)) ^ (160 - c))) *
    (Sc * (10 ^ 31 - 3384))

def posBaseWGe (c : Nat) : Nat :=
  (560227709747861399187319382270000000000000000000000000000000 *
    ((10 ^ 40 : Nat) ^ (160 - c))) *
    (10 ^ 18 * 10 ^ 31)

def PosShiftGeBudgetOk (m c x : Nat) (r : Int) : Prop :=
  posPhaseNatGe m c ≤ lnErrArg r ∧
    wadRayNum x * (posBaseWGe c * lnErrQ) ≤
      (posBaseYGe m c * (lnErrQ + posAvailGe m c r)) * wadRayStrictDen

def PosShiftGeBudgetIneqOk (m c x : Nat) (r : Int) : Prop :=
  wadRayNum x * (posBaseWGe c * lnErrQ) ≤
    (posBaseYGe m c * (lnErrQ + posAvailGe m c r)) * wadRayStrictDen

def posConstNat (c : Nat) : Nat :=
  (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
    BIASc * twoPow27N * lnErrorBoundDen

def posNegXNat (m : Nat) : Nat :=
  (-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen

def posPhaseNatLt (m c : Nat) : Nat :=
  posConstNat c - posNegXNat m

def posAvailLt (m c : Nat) (r : Int) : Nat :=
  lnErrArg r - posPhaseNatLt m c

def posBaseYLt (m c : Nat) : Nat :=
  ((2 * (10 ^ 40 - 1)) ^ (160 - c) * (Sc * (10 ^ 31 - 3384))) *
    (m * 9999999999999999999999999996615)

def posBaseWLt (c : Nat) : Nat :=
  (((10 ^ 40 : Nat) ^ (160 - c) * (10 ^ 18 * 10 ^ 31)) *
    560227709747861399187319382270000000000000000000000000000000)

def PosShiftLtBudgetOk (m c x : Nat) (r : Int) : Prop :=
  posNegXNat m ≤ posConstNat c ∧
    posPhaseNatLt m c ≤ lnErrArg r ∧
      wadRayNum x * (posBaseWLt c * lnErrQ) ≤
        (posBaseYLt m c * (lnErrQ + posAvailLt m c r)) * wadRayStrictDen

def PosShiftLtBudgetIneqOk (m c x : Nat) (r : Int) : Prop :=
  wadRayNum x * (posBaseWLt c * lnErrQ) ≤
    (posBaseYLt m c * (lnErrQ + posAvailLt m c r)) * wadRayStrictDen

def PosShiftGeTopBudgetIneqOk (m c : Nat) : Prop :=
  PosShiftGeBudgetIneqOk m c (posTopX c m) (int256 (lnTail (evmSub 160 c) m))

def PosShiftLtTopBudgetIneqOk (m c : Nat) : Prop :=
  PosShiftLtBudgetIneqOk m c (posTopX c m) (int256 (lnTail (evmSub 160 c) m))

def lnPhaseExtraArg : Nat := lnErrorExtraNum * twoPow99N

def PosShiftGePhaseDirectOk (n m c : Nat) : Prop :=
  sumGE n (posPhaseNatGe m c + lnPhaseExtraArg) lnErrQ (posTopX c m) (10 ^ 18)

def PosShiftLtPhaseDirectOk (n m c : Nat) : Prop :=
  sumGE n (posPhaseNatLt m c + lnPhaseExtraArg) lnErrQ (posTopX c m) (10 ^ 18)

def minPosAvail : Nat := lnPhaseExtraArg + twoPow27N * lnErrorBoundDen

def PosShiftGeMinPhaseDirectOk (n m c : Nat) : Prop :=
  sumGE n (posPhaseNatGe m c + minPosAvail) lnErrQ (posTopX c m) (10 ^ 18)

def PosShiftLtMinPhaseDirectOk (n m c : Nat) : Prop :=
  sumGE n (posPhaseNatLt m c + minPosAvail) lnErrQ (posTopX c m) (10 ^ 18)

def lnDirectGapArg : Nat := lnErrorDirectResidueGap * twoPow27N * lnErrorBoundDen

def PosShiftGePhaseGapDirectOk (n m c : Nat) : Prop :=
  sumGE n (posPhaseNatGe m c + lnPhaseExtraArg + lnDirectGapArg) lnErrQ
    (posTopX c m) (10 ^ 18)

def PosShiftLtPhaseGapDirectOk (n m c : Nat) : Prop :=
  sumGE n (posPhaseNatLt m c + lnPhaseExtraArg + lnDirectGapArg) lnErrQ
    (posTopX c m) (10 ^ 18)

end LnFloorCert
