import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell10 : checkCoverK kB certErrLtLit 40921604216002285725209949215 40987649777297210133226675106
    [66045561294924408016725891] = true := by
  decide +kernel

end LnFloorCert
