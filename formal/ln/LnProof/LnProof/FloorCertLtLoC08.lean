import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell08 : checkCoverK 38000 certLtLoLit 11091773201185835211973625643016 11885210362657835211973625643016
    [793437161472000000000000000000] = true := by
  decide +kernel

end LnFloorCert
