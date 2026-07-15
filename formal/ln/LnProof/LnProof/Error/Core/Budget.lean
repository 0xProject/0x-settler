import LnProof.Floor.CutEquiv
import LnProof.Error.Cert
import LnProof.Error.Core.CutDefs

/-!
# Error bound — Budget

The natural-number phase split and the minimum available closing margin.
-/

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

namespace LnFloorCert

open LnYul LnFloor Common.Exp Common.Poly

attribute [local irreducible] lnWadToRayBody


def posConstNat (c : Nat) : Nat :=
  (160 - c) * ((LN2c * twoPow27N) * lnErrorBoundDen) +
    BIASc * twoPow27N * lnErrorBoundDen

def posNegXNat (m : Nat) : Nat :=
  (-int256 (x1W (zWord m))).toNat * lnPhaseScaleN * lnErrorBoundDen

def posPhaseNatLt (m c : Nat) : Nat :=
  posConstNat c - posNegXNat m

def posAvailLt (m c : Nat) (r : Int) : Nat :=
  lnErrArg r - posPhaseNatLt m c

def lnPhaseExtraArg : Nat := lnErrorExtraNum * twoPow99N

def minPosAvail : Nat := lnPhaseExtraArg + twoPow27N * lnErrorBoundDen

end LnFloorCert
