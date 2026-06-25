import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell09 : checkCoverK kB certErrLtLit 41043045905047721566882051166 43074909657573168724990774475
    [2031863752525447158108723309] = true := by
  decide +kernel

end LnFloorCert
