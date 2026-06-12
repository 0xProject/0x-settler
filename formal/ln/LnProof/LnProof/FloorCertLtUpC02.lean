import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell02 : checkCoverK 38000 certLtUpLit 10250644801825835211973625643010 10297300801825835211973625643010
    [46656000000000000000000000000] = true := by
  decide +kernel

end LnFloorCert
