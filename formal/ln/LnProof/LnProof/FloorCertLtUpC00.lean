import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell00 : checkCoverK kB certLtUpLit 39614081257132168796771975168 39982534672164782411896871713
    [368082752165888438750145608, 370662866725176374750936] = true := by
  decide +kernel

end LnFloorCert
