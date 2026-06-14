import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell02 : checkCoverK kB certGeLoLit 15678149369545251819195376186277 16051397369545251819195376186277
    [373248000000000000000000000000] = true := by
  decide +kernel

end LnFloorCert
