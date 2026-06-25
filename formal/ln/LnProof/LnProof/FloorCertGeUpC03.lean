import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell03 : checkCoverK kB certGeUpLit 65565966845362846449121124692 66268224935948723932208112262
    [702258090585877483086987570] = true := by
  decide +kernel

end LnFloorCert
