import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell06 : checkCoverK kB certLtLoLit 40933137699355212682659008290 41019543030322903743594235649
    [86405330967691060935227359] = true := by
  decide +kernel

end LnFloorCert
