import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell03 : checkCoverK kB certGeLoLit 16051397369545251819195376186278 17395090169545251819195376186278
    [1343692800000000000000000000000] = true := by
  decide +kernel

end LnFloorCert
