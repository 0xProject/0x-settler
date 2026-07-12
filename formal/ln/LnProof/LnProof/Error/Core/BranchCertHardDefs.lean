import LnProof.Error.Core.Direct

open FormalYul
open FormalYul.Preservation

namespace LnFloorCert

open LnYul LnFloor

def posShiftLtPhaseGapDirectOkB (m c : Nat) : Bool :=
  sumGEB 320 (posPhaseNatLt m c + lnPhaseExtraArg + lnDirectGapArg) lnErrQ
    (posTopX c m) (10 ^ 18)

def hardMantissaLtGapBranchB (c : Nat) : Bool :=
  directResidueGapOkB lnErrorHardMantissa c
      (int256 (lnTail (evmSub 160 c) lnErrorHardMantissa)) &&
    posShiftLtPhaseGapDirectOkB lnErrorHardMantissa c

end LnFloorCert
