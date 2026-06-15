import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell09 : checkCoverK kB certLtLoLit 43340936784615056347798031795 43553475214845372217317803462
    [212538430230315869519771667] = true := by
  decide +kernel

end LnFloorCert
