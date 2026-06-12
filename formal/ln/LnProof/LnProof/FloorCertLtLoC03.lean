import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell03 : checkCoverK 38000 certLtLoLit 10180228801825835211973625643011 10348190401825835211973625643011
    [167961600000000000000000000000] = true := by
  decide +kernel

end LnFloorCert
