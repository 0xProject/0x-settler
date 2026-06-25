import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell06 : checkCoverK kB certErrLtLit 40679997165554683551591585808 40924139963113827378389531693
    [244142797559143826797945885] = true := by
  decide +kernel

end LnFloorCert
