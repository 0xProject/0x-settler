import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell15 : checkCoverK kB certErrLtLit 49441198747998157922924465951 52208342513818930575475816108
    [2767143765820772652551350157] = true := by
  decide +kernel

end LnFloorCert
