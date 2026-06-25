import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell10 : checkCoverK kB certLtUpLit 42146662162229712555615056323 44752276460150783290898176684
    [2605614297921070735283120361] = true := by
  decide +kernel

end LnFloorCert
