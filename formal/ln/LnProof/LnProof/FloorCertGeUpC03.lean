import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell03 : checkCoverK 38000 certGeUpLit 16378565369545251819195376186278 16714488569545251819195376186278
    [335923200000000000000000000000] = true := by
  decide +kernel

end LnFloorCert
