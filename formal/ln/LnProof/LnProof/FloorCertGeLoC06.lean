import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell06 : checkCoverK kB certGeLoLit 69643680272268497720544738510 73761687789119228727691347873
    [4115587520191931922188390275, 2419996658799084958219087] = true := by
  decide +kernel

end LnFloorCert
