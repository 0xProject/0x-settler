import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell05 : checkCoverK kB certLtUpLit 40276316995481393586173805060 41692401823923536401685262437
    [1416084828442142815511457377] = true := by
  decide +kernel

end LnFloorCert
