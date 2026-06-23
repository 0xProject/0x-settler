import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell03 : checkCoverK kB certGeLoLit 64929052012891719377728977368 68717504609657537844941640470
    [3783852446681905466239449795, 4600150083913000973213306] = true := by
  decide +kernel

end LnFloorCert
