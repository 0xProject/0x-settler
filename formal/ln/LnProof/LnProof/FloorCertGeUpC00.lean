import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell00 : checkCoverK kB certGeUpLit 14341829369545251819195376186275 15212167328226586335452577096833
    [870337958681334516257200910558] = true := by
  decide +kernel

end LnFloorCert
