import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell10 : checkCoverK kB certErrLtLit 43461765492999010618411064513 43645705213556298311291468356
    [183939720557287692880403843] = true := by
  decide +kernel

end LnFloorCert
