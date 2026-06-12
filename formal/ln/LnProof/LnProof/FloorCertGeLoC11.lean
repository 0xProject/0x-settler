import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell11 : checkCoverK 38000 certGeLoLit 19835348970720956005264548083724 19952161587712529772726802791418
    [116812616991573767462254707694] = true := by
  decide +kernel

end LnFloorCert
