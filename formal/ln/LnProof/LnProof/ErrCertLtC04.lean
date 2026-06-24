import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell04 : checkCoverK kB certErrLtLit 39760668564320063520044754513 39765961139795848653992550332
    [5292575475785133947795819] = true := by
  decide +kernel

end LnFloorCert
