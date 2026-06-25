import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell02 : checkCoverK kB certGeUpLit 60261195396300777138610597147 65565966845362846449121124691
    [5304771449062069310510527544] = true := by
  decide +kernel

end LnFloorCert
