import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell09 : checkCoverK kB certGeLoLit 74497159690857676763262189493 77437517811705333581000648120
    [2940358120847656817738458627] = true := by
  decide +kernel

end LnFloorCert
