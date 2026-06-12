import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell06 : checkCoverK 38000 certGeLoLit 18241616633545251819195376186281 18731392659145251819195376186281
    [489776025600000000000000000000] = true := by
  decide +kernel

end LnFloorCert
