import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell12 : checkCoverK kB certLtLoLit 12107816687380846383659741095858 13288514059040829116868868842637
    [1180697371659982733209127746779] = true := by
  decide +kernel

end LnFloorCert
