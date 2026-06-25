import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell13 : checkCoverK kB certErrLtLit 46777373364869912303362302354 47278853413441676783280697546
    [501480048571764479918395192] = true := by
  decide +kernel

end LnFloorCert
