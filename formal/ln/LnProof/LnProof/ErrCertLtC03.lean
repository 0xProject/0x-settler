import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell03 : checkCoverK kB certErrLtLit 39754544997383943847916639873 39771161441046609927456741695
    [16616443662666079540101822] = true := by
  decide +kernel

end LnFloorCert
