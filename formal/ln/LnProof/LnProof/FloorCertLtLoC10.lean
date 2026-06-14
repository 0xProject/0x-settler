import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell10 : checkCoverK kB certLtLoLit 11146581489870108061665359760579 11975319732385395244128879337329
    [828738242515287182463519576750] = true := by
  decide +kernel

end LnFloorCert
