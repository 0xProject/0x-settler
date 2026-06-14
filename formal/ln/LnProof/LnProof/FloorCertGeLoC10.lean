import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell10 : checkCoverK kB certGeLoLit 19824760229103743917401162234565 19931765688779127819938665734675
    [107005459675383902537503500110] = true := by
  decide +kernel

end LnFloorCert
