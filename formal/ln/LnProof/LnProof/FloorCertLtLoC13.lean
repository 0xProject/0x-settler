import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell13 : checkCoverK kB certLtLoLit 13288514059040829116868868842638 13495933876257960396238152163105
    [207419817217131279369283320467] = true := by
  decide +kernel

end LnFloorCert
