import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell01 : checkCoverK kB certLtLoLit 10161039087138297937552302321359 10171666388457316730463887800014
    [10627301319018792911585478655] = true := by
  decide +kernel

end LnFloorCert
