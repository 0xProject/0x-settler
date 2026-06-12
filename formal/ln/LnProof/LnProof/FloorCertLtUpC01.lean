import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell01 : checkCoverK 38000 certLtUpLit 10198804801825835211973625643009 10250644801825835211973625643009
    [51840000000000000000000000000] = true := by
  decide +kernel

end LnFloorCert
