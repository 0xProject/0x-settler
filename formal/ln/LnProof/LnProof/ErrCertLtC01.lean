import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell01 : checkCoverK kB certErrLtLit 39691126742571296271047700503 39731844495833091299568641514
    [40717753261795028520941011] = true := by
  decide +kernel

end LnFloorCert
