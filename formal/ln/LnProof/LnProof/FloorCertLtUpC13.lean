import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell13 : checkCoverK kB certLtUpLit 49100597176785563576919508300 49670405993033439910727072903
    [569808816247876333807564603] = true := by
  decide +kernel

end LnFloorCert
