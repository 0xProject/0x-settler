import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell07 : checkCoverK kB certLtLoLit 11045875788223987512547846876914 11157540185491473638622902634206
    [111664397267486126075055757292] = true := by
  decide +kernel

end LnFloorCert
