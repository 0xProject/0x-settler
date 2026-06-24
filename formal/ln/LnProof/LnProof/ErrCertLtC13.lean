import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell13 : checkCoverK kB certErrLtLit 47304945315436282108986587295 51917938338423636963586449826
    [4612993022987354854599862531] = true := by
  decide +kernel

end LnFloorCert
