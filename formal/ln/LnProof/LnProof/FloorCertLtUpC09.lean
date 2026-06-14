import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell09 : checkCoverK kB certLtUpLit 12580407414500243265481207840048 12790326440757707523851639277546
    [209919026257464258370431437498] = true := by
  decide +kernel

end LnFloorCert
