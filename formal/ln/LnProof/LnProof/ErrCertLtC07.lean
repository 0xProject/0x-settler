import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell07 : checkCoverK kB certErrLtLit 40924139963113827378389531694 40994349676318877769223711475
    [70209713205050390834179781] = true := by
  decide +kernel

end LnFloorCert
