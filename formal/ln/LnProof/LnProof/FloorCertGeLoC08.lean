import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell08 : checkCoverK kB certGeLoLit 19943464632857537495188824650086 20003729176681302270498866098359
    [60264543823764775310041448273] = true := by
  decide +kernel

end LnFloorCert
