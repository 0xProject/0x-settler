import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell00 : checkCoverK kB certLtUpLit 10141204801825835211973625643008 10236733219469637195766410765227
    [95528417643801983792785122219] = true := by
  decide +kernel

end LnFloorCert
