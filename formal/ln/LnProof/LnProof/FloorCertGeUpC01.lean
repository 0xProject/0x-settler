import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell01 : checkCoverK kB certGeUpLit 59266081817351235913474286846 60261195396300777138610597146
    [995113578949541225136310300] = true := by
  decide +kernel

end LnFloorCert
