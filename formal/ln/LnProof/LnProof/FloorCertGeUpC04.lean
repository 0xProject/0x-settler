import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell04 : checkCoverK kB certGeUpLit 66326042884080760773638716082 71285921383811406182045145578
    [4959878499730645408406429496] = true := by
  decide +kernel

end LnFloorCert
