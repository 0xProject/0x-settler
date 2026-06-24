import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell07 : checkCoverK kB certErrLtLit 39770663872413954292287692848 39776734234069348046975027352
    [6070361655393754687334504] = true := by
  decide +kernel

end LnFloorCert
