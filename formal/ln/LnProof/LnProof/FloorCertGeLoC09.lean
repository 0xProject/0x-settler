import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell09 : checkCoverK kB certGeLoLit 74497159690857676763262189493 77437517811705333581000648120
    [2939189762470794084770802393, 1168358376862732967656233] = true := by
  decide +kernel

end LnFloorCert
