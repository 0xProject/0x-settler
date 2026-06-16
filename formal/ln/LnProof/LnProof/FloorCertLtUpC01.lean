import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell01 : checkCoverK kB certLtUpLit 39982534672164782411896871714 40150853919271982033591711249
    [168319247107199621694839535] = true := by
  decide +kernel

end LnFloorCert
