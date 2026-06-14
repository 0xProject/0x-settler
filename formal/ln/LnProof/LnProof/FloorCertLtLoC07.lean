import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell07 : checkCoverK kB certLtLoLit 10981573595425835211973625643015 11091773201185835211973625643015
    [110199605760000000000000000000] = true := by
  decide +kernel

end LnFloorCert
