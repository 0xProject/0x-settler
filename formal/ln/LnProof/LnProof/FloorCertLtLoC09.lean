import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell09 : checkCoverK kB certLtLoLit 43347765646151204775670435097 43555340935173254406944988025
    [207575289022049631274552928] = true := by
  decide +kernel

end LnFloorCert
