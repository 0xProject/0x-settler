import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell14 : checkCoverK kB certErrLtLit 47278853413441676783280697547 49441198747998157922924465950
    [2162345334556481139643768403] = true := by
  decide +kernel

end LnFloorCert
