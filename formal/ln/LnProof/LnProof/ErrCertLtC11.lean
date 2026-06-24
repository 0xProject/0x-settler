import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell11 : checkCoverK kB certErrLtLit 43645705213556298311291468357 46790509509991214314127230409
    [3144804296434916002835762052] = true := by
  decide +kernel

end LnFloorCert
