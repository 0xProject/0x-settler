import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell04 : checkCoverK kB certErrLtLit 39771161441046609927456741696 40680904853992493020014255642
    [909743412945883092557513946] = true := by
  decide +kernel

end LnFloorCert
