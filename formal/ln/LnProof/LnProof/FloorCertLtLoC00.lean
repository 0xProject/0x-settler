import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell00 : checkCoverK kB certLtLoLit 10141204801825835211973625643008 10161039087138297937552302321358
    [19834285312462725578676678350] = true := by
  decide +kernel

end LnFloorCert
