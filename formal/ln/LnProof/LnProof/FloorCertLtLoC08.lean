import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell08 : checkCoverK kB certLtLoLit 42508799051393563554355157299 43347765646151204775670435096
    [838966594757641221315277797] = true := by
  decide +kernel

end LnFloorCert
