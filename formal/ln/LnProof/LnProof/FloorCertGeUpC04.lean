import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell04 : checkCoverK 38000 certGeUpLit 16714488569545251819195376186279 17319150329545251819195376186279
    [604661760000000000000000000000] = true := by
  decide +kernel

end LnFloorCert
