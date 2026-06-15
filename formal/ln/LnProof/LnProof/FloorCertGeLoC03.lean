import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell03 : checkCoverK kB certGeLoLit 64927737322685640209302100707 68717226458158102762251661877
    [3789489135472462552949561170] = true := by
  decide +kernel

end LnFloorCert
