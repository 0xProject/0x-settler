import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell11 : checkCoverK kB certLtLoLit 46779428052747433029299757937 47296264120598942405857135301
    [502936420367312898591965414, 13899647484196477965411949] = true := by
  decide +kernel

end LnFloorCert
