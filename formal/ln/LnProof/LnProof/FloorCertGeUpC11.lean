import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell11 : checkCoverK kB certGeUpLit 78595188666574508701639272525 78835627367648889913153387938
    [240438701074381211514115413] = true := by
  decide +kernel

end LnFloorCert
