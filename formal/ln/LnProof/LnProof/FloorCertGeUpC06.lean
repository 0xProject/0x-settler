import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell06 : checkCoverK 38000 certGeUpLit 17863345913545251819195376186281 18353121939145251819195376186281
    [489776025600000000000000000000] = true := by
  decide +kernel

end LnFloorCert
