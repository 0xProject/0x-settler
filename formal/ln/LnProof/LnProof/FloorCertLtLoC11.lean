import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell11 : checkCoverK kB certLtLoLit 11975319732385395244128879337330 12107816687380846383659741095857
    [132496954995451139530861758527] = true := by
  decide +kernel

end LnFloorCert
