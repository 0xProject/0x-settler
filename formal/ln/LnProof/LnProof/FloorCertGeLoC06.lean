import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell06 : checkCoverK kB certGeLoLit 69643680272268497720544738510 73761687789119228727691347873
    [4118007516850731007146609363] = true := by
  decide +kernel

end LnFloorCert
