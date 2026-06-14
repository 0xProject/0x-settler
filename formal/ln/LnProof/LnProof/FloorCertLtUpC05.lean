import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell05 : checkCoverK kB certLtUpLit 10318581351720418835446063066152 10675431702120254763124784810886
    [356850350399835927678721744734] = true := by
  decide +kernel

end LnFloorCert
