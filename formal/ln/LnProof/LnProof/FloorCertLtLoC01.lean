import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell01 : checkCoverK kB certLtLoLit 10161770191662089796732559035026 10173867602363700194303868407035
    [12097410701610397571309372009] = true := by
  decide +kernel

end LnFloorCert
