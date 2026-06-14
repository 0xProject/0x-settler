import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell14 : checkCoverK kB certLtLoLit 13495933876257960396238152163106 14341829369545251819195376186183
    [845895493287291422957224023077] = true := by
  decide +kernel

end LnFloorCert
