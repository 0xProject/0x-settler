import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell08 : checkCoverK kB certGeLoLit 74347359659513480232328600325 74497159690857676763262189492
    [149800031344196530933589167] = true := by
  decide +kernel

end LnFloorCert
