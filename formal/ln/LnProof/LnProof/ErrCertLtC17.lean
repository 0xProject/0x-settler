import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell17 : checkCoverK kB certErrLtLit 46772661970268323857756182434 47265409858234429269501593572
    [492747887966105411745411138] = true := by
  decide +kernel

end LnFloorCert
