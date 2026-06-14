import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell04 : checkCoverK kB certGeLoLit 17598736452200977411008546368196 17725958073728107644688556445028
    [127221621527130233680010076832] = true := by
  decide +kernel

end LnFloorCert
