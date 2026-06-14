import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell02 : checkCoverK kB certGeUpLit 15632069369545251819195376186277 16378565369545251819195376186277
    [746496000000000000000000000000] = true := by
  decide +kernel

end LnFloorCert
