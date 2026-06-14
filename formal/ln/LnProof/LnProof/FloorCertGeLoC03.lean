import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell03 : checkCoverK kB certGeLoLit 16697056551612731524305339424316 17598736452200977411008546368195
    [901679900588245886703206943879] = true := by
  decide +kernel

end LnFloorCert
