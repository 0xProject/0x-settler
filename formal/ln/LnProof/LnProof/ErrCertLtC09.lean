import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell09 : checkCoverK kB certErrLtLit 40679522109640282356488826988 40921604216002285725209949214
    [242082106362003368721122226] = true := by
  decide +kernel

end LnFloorCert
