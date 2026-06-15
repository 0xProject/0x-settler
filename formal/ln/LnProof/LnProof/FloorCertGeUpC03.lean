import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell03 : checkCoverK kB certGeUpLit 65647205322201657485063864880 66326042884080760773638716081
    [678837561879103288574851201] = true := by
  decide +kernel

end LnFloorCert
