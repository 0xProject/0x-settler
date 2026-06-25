import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell03 : checkCoverK kB certErrLtLit 39751783327094435418800986831 39763891854368929726387401070
    [12108527274494307586414239] = true := by
  decide +kernel

end LnFloorCert
