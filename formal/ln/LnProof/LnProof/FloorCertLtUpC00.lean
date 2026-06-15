import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell00 : checkCoverK kB certLtUpLit 39614081257132168796771975168 39982530726060180992616285302
    [368449468928012195844310134] = true := by
  decide +kernel

end LnFloorCert
