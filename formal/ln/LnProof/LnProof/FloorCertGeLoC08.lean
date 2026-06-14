import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell08 : checkCoverK kB certGeLoLit 19034951989452419220406092183060 19074220051933406024237855970763
    [39268062480986803831763787703] = true := by
  decide +kernel

end LnFloorCert
