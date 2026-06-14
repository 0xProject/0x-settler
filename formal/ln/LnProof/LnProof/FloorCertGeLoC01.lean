import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell01 : checkCoverK kB certGeLoLit 15263429369545251819195376186276 15678149369545251819195376186276
    [414720000000000000000000000000] = true := by
  decide +kernel

end LnFloorCert
