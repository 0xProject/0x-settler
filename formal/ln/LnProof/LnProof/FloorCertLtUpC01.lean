import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell01 : checkCoverK kB certLtUpLit 39982534672164782411896871714 40150853919271982033591711249
    [167178714878835265161945165, 1140532228364356532894369] = true := by
  decide +kernel

end LnFloorCert
