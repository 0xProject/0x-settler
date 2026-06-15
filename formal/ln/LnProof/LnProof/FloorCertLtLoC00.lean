import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell00 : checkCoverK kB certLtLoLit 39614081257132168796771975168 39691571409046729502659323845
    [77490151914560705887348677] = true := by
  decide +kernel

end LnFloorCert
