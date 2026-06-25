import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell16 : checkCoverK kB certErrLtLit 52208342513818930575475816109 53036600108885143092541888944
    [828257595066212517066072835] = true := by
  decide +kernel

end LnFloorCert
