import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell11 : checkCoverK kB certLtLoLit 46779569004398866896767989131 47296288103334780980946196294
    [516719098935914084178207163] = true := by
  decide +kernel

end LnFloorCert
