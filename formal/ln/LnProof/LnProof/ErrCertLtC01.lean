import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell01 : checkCoverK kB certErrLtLit 39690713995389999812980837315 39730677041036699034014990826
    [39963045646699221034153511] = true := by
  decide +kernel

end LnFloorCert
