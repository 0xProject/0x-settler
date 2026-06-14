import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell00 : checkCoverK kB certLtLoLit 10141204801825835211973625643008 10161770191662089796732559035025
    [20565389836254584758933392017] = true := by
  decide +kernel

end LnFloorCert
