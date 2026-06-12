import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell10 : checkCoverK 38000 certLtUpLit 12705514739080235211973625643018 14341829369545251819195376186183
    [1636314630465016607221750543165] = true := by
  decide +kernel

end LnFloorCert
