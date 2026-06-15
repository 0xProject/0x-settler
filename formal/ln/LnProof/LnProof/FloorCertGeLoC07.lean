import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell07 : checkCoverK kB certGeLoLit 73761496465424587311876899022 74347248156118664616646853613
    [585751690694077304769954591] = true := by
  decide +kernel

end LnFloorCert
