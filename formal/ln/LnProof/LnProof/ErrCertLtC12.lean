import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell12 : checkCoverK kB certErrLtLit 46790509509991214314127230410 47304945315436282108986587294
    [514435805445067794859356884] = true := by
  decide +kernel

end LnFloorCert
