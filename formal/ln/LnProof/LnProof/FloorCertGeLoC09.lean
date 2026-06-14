import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell09 : checkCoverK kB certGeLoLit 20003729176681302270498866098360 20282409603651670423947251286015
    [278680426970368153448385187655] = true := by
  decide +kernel

end LnFloorCert
