import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell14 : checkCoverK kB certErrLtLit 43087646344191582790285854568 43441958359528469510743996388
    [354312015336886720458141820] = true := by
  decide +kernel

end LnFloorCert
