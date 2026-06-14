import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell08 : checkCoverK kB certLtLoLit 10804067352168065028243107714129 11083194856947080296999923602747
    [279127504779015268756815888618] = true := by
  decide +kernel

end LnFloorCert
