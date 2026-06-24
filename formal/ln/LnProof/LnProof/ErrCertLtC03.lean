import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell03 : checkCoverK kB certErrLtLit 39750332389280211543769847733 39760668564320063520044754512
    [10336175039851976274906779] = true := by
  decide +kernel

end LnFloorCert
