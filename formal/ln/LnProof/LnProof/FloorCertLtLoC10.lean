import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell10 : checkCoverK kB certLtLoLit 12167033336528931136866442932389 13312231794559356263903131156023
    [1145198458030425127036688223634] = true := by
  decide +kernel

end LnFloorCert
