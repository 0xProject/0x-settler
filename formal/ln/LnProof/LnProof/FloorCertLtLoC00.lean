import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell00 : checkCoverK kB certLtLoLit 39614081257132168796771975168 39691568842842447562319269665
    [77259500184707272552737754, 228085525571492994556742] = true := by
  decide +kernel

end LnFloorCert
