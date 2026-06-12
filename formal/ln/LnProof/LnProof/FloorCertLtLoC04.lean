import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell04 : checkCoverK 38000 certLtLoLit 10348190401825835211973625643012 10423773121825835211973625643012
    [75582720000000000000000000000] = true := by
  decide +kernel

end LnFloorCert
