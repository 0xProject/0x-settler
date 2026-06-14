import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell03 : checkCoverK kB certGeLoLit 17554148321139982097229836138648 17786173684522105145630735255165
    [232025363382123048400899116517] = true := by
  decide +kernel

end LnFloorCert
