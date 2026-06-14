import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell09 : checkCoverK kB certLtLoLit 11083194856947080296999923602748 11146581489870108061665359760578
    [63386632923027764665436157830] = true := by
  decide +kernel

end LnFloorCert
