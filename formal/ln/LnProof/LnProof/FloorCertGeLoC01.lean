import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell01 : checkCoverK kB certGeLoLit 15948890630125408368526546481899 16237965730166783515045182532374
    [289075100041375146518636050475] = true := by
  decide +kernel

end LnFloorCert
