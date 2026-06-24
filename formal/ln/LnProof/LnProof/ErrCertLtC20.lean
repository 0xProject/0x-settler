import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell20 : checkCoverK kB certErrLtLit 51996533350514057035622956907 52718050121226925508670314994
    [721516770712868473047358087] = true := by
  decide +kernel

end LnFloorCert
