import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell08 : checkCoverK kB certLtUpLit 11555030854945835211973625643016 12348468016417835211973625643016
    [793437161472000000000000000000] = true := by
  decide +kernel

end LnFloorCert
