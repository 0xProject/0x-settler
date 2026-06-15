import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell00 : checkCoverK kB certLtUpLit 39614081257132168796771975168 39982534672164782411896871713
    [368453415032613615124896545] = true := by
  decide +kernel

end LnFloorCert
