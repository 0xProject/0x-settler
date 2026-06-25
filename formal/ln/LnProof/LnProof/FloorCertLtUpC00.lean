import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell00 : checkCoverK kB certLtUpLit 39614081257132168796771975168 39982094489912265292386939330
    [368013232780096495614964162] = true := by
  decide +kernel

end LnFloorCert
