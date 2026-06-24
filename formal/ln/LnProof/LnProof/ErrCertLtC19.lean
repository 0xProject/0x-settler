import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell19 : checkCoverK kB certErrLtLit 47863312455617981068416176221 51996533350514057035622956906
    [4133220894896075967206780685] = true := by
  decide +kernel

end LnFloorCert
