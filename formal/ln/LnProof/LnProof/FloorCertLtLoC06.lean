import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell06 : checkCoverK kB certLtLoLit 10491797569825835211973625643014 10981573595425835211973625643014
    [489776025600000000000000000000] = true := by
  decide +kernel

end LnFloorCert
