import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell11 : checkCoverK kB certLtUpLit 11567222306833343375585957498288 11614401749478021771482220450251
    [47179442644678395896262951963] = true := by
  decide +kernel

end LnFloorCert
