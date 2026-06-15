import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell10 : checkCoverK kB certLtLoLit 43553475214845372217317803463 46779428052747433029299757936
    [3225952837902060811981954473] = true := by
  decide +kernel

end LnFloorCert
