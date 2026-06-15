import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell11 : checkCoverK kB certGeLoLit 77857297359333941978235389795 77947573405191424248689952843
    [90276045857482270454563048] = true := by
  decide +kernel

end LnFloorCert
