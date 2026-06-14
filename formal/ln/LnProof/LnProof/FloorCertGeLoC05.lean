import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell05 : checkCoverK kB certGeLoLit 18884357842035863895902153040986 19067888394773041807616703749812
    [183530552737177911714550708826] = true := by
  decide +kernel

end LnFloorCert
