import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell10 : checkCoverK kB certLtUpLit 44761456068401282094658552448 45182202408663635743116208964
    [420746340262353648457656516] = true := by
  decide +kernel

end LnFloorCert
