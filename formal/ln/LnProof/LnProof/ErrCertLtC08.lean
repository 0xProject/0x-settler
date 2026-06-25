import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell08 : checkCoverK kB certErrLtLit 40994349676318877769223711476 41043045905047721566882051165
    [48696228728843797658339689] = true := by
  decide +kernel

end LnFloorCert
