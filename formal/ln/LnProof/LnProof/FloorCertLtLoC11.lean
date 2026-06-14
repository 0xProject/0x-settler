import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell11 : checkCoverK kB certLtLoLit 13312231794559356263903131156024 13764455152493014279112910224238
    [452223357933658015209779068214] = true := by
  decide +kernel

end LnFloorCert
