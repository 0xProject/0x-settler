import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell01 : checkCoverK kB certGeUpLit 14802629369545251819195376186276 15632069369545251819195376186276
    [829440000000000000000000000000] = true := by
  decide +kernel

end LnFloorCert
