import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell13 : checkCoverK kB certGeUpLit 78893863486352981843045626397 78941888558111820679980811876
    [48025071758838836935185479] = true := by
  decide +kernel

end LnFloorCert
