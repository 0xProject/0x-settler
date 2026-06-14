import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell00 : checkCoverK kB certLtLoLit 10141204801825835211973625643008 10155604801825835211973625643008
    [14400000000000000000000000000] = true := by
  decide +kernel

end LnFloorCert
