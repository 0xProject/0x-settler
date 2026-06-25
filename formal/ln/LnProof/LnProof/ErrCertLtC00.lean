import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell00 : checkCoverK kB certErrLtLit 39614081257132168796771975168 39690713995389999812980837314
    [76632738257831016208862146] = true := by
  decide +kernel

end LnFloorCert
