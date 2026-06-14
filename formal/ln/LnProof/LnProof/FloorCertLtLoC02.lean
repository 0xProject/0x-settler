import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell02 : checkCoverK kB certLtLoLit 10171666388457316730463887800015 10177940795541626959104557434485
    [6274407084310228640669634470] = true := by
  decide +kernel

end LnFloorCert
