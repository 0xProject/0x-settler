import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell08 : checkCoverK kB certLtLoLit 11157540185491473638622902634207 11984914669923891730780665874658
    [827374484432418092157763240451] = true := by
  decide +kernel

end LnFloorCert
