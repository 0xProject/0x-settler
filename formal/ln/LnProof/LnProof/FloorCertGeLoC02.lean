import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell02 : checkCoverK kB certGeLoLit 63042223622777199713651466027 64927737322685640209302100706
    [1885513699908440495650634679] = true := by
  decide +kernel

end LnFloorCert
