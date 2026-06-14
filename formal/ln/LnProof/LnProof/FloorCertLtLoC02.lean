import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell02 : checkCoverK kB certLtLoLit 10173867602363700194303868407036 10185047743608951581783796515312
    [11180141245251387479928108276] = true := by
  decide +kernel

end LnFloorCert
