import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell05 : checkCoverK kB certGeLoLit 17725958073728107644688556445029 17852105151840201335476027974486
    [126147078112093690787471529457] = true := by
  decide +kernel

end LnFloorCert
