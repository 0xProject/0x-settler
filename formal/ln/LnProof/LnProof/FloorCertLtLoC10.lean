import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell10 : checkCoverK kB certLtLoLit 12242257085320235211973625643018 12884941186112555211973625643018
    [642684100792320000000000000000] = true := by
  decide +kernel

end LnFloorCert
