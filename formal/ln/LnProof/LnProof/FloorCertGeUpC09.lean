import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell09 : checkCoverK kB certGeUpLit 76368615273267926498199066889 76512522319826533298339061377
    [143907046558606800139994488] = true := by
  decide +kernel

end LnFloorCert
