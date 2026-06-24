import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell09 : checkCoverK kB certErrLtLit 43095658317834209710916769051 43461765492999010618411064512
    [366107175164800907494295461] = true := by
  decide +kernel

end LnFloorCert
