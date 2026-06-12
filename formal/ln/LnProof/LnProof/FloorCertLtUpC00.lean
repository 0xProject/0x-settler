import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell00 : checkCoverK 38000 certLtUpLit 10141204801825835211973625643008 10198804801825835211973625643008
    [57600000000000000000000000000] = true := by
  decide +kernel

end LnFloorCert
