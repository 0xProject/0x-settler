import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell00 : checkCoverK kB certGeUpLit 14341829369545251819195376186275 14802629369545251819195376186275
    [460800000000000000000000000000] = true := by
  decide +kernel

end LnFloorCert
