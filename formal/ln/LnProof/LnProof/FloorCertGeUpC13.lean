import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell13 : checkCoverK kB certGeUpLit 20198185050312597011198675301887 20217130875292592156275203260040
    [18945824979995145076527958153] = true := by
  decide +kernel

end LnFloorCert
