import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell02 : checkCoverK kB certErrLtLit 39730677041036699034014990827 39751783327094435418800986830
    [21106286057736384785996003] = true := by
  decide +kernel

end LnFloorCert
