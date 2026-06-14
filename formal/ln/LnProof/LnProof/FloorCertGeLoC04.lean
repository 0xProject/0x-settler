import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell04 : checkCoverK kB certGeLoLit 17786173684522105145630735255166 18884357842035863895902153040985
    [1098184157513758750271417785819] = true := by
  decide +kernel

end LnFloorCert
