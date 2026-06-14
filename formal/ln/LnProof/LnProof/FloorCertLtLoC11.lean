import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell11 : checkCoverK kB certLtLoLit 12884941186112555211973625643019 13463356876825643211973625643019
    [578415690713088000000000000000] = true := by
  decide +kernel

end LnFloorCert
