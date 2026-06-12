import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell12 : checkCoverK 38000 certGeLoLit 19952161587712529772726802791419 20282409603651670423947251286015
    [330248015939140651220448494596] = true := by
  decide +kernel

end LnFloorCert
