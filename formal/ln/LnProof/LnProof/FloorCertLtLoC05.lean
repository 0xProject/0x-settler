import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell05 : checkCoverK kB certLtLoLit 10423773121825835211973625643013 10491797569825835211973625643013
    [68024448000000000000000000000] = true := by
  decide +kernel

end LnFloorCert
