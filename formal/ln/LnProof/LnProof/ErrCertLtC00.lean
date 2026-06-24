import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell00 : checkCoverK kB certErrLtLit 39614081257132168796771975168 39690487033155318831492514644
    [76405776023150034720539476] = true := by
  decide +kernel

end LnFloorCert
