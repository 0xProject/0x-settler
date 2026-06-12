import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell00 : checkCoverK 38000 certGeLoLit 14341829369545251819195376186275 15263429369545251819195376186275
    [921600000000000000000000000000] = true := by
  decide +kernel

end LnFloorCert
