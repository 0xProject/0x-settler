import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell07 : checkCoverK kB certLtLoLit 41019543030322903743594235650 42434861454155548723387563152
    [681805913666974410691864606, 733512510165670569101462895] = true := by
  decide +kernel

end LnFloorCert
