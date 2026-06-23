import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell05 : checkCoverK kB certGeLoLit 69233132140651152842861403917 69643680272268497720544738509
    [289791708622739137467668003, 120756422994605740215666588] = true := by
  decide +kernel

end LnFloorCert
