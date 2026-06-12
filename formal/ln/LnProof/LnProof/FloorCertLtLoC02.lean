import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell02 : checkCoverK 38000 certLtLoLit 10168564801825835211973625643010 10180228801825835211973625643010
    [11664000000000000000000000000] = true := by
  decide +kernel

end LnFloorCert
