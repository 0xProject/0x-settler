import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell11 : checkCoverK kB certGeLoLit 19931765688779127819938665734676 19955291445289458852554233347635
    [23525756510331032615567612959] = true := by
  decide +kernel

end LnFloorCert
