import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell06 : checkCoverK kB certLtLoLit 40933163684002996933851849392 41019616312100785763631764706
    [86452628097788829779915314] = true := by
  decide +kernel

end LnFloorCert
