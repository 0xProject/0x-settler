import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell09 : checkCoverK kB certGeLoLit 19074220051933406024237855970764 19824760229103743917401162234564
    [750540177170337893163306263800] = true := by
  decide +kernel

end LnFloorCert
