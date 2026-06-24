import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell14 : checkCoverK kB certErrLtLit 51917938338423636963586449827 52819343388154448027094034823
    [901405049730811063507584996] = true := by
  decide +kernel

end LnFloorCert
