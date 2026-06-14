import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell00 : checkCoverK kB certGeUpLit 14341829369545251819195376186275 15175514278996281049189740636296
    [833684909451029229994364450021] = true := by
  decide +kernel

end LnFloorCert
