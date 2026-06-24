import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell00 : checkCoverK kB certErrLtLit 39614081257132168796771975168 39691126742571296271047700502
    [77045485439127474275725334] = true := by
  decide +kernel

end LnFloorCert
