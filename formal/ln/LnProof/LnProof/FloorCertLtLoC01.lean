import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell01 : checkCoverK kB certLtLoLit 10155604801825835211973625643009 10168564801825835211973625643009
    [12960000000000000000000000000] = true := by
  decide +kernel

end LnFloorCert
