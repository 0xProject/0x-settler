import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell05 : checkCoverK 38000 certGeUpLit 17319150329545251819195376186280 17863345913545251819195376186280
    [544195584000000000000000000000] = true := by
  decide +kernel

end LnFloorCert
