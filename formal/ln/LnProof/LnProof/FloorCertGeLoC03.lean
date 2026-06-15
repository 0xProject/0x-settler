import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell03 : checkCoverK kB certGeLoLit 64929052012891719377728977368 68717504609657537844941640470
    [3788452596765818467212663102] = true := by
  decide +kernel

end LnFloorCert
