import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell06 : checkCoverK kB certGeUpLit 71968494449566398338160691003 72409504182901287012502905605
    [441009733334888674342214602] = true := by
  decide +kernel

end LnFloorCert
