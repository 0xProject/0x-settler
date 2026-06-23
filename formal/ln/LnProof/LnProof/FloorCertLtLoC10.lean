import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell10 : checkCoverK kB certLtLoLit 43553475214845372217317803463 46779428052747433029299757936
    [3223246483088125253183381252, 2706354813935558798573220] = true := by
  decide +kernel

end LnFloorCert
