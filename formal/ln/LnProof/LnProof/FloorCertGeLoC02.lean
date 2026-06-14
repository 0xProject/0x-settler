import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell02 : checkCoverK kB certGeLoLit 16237965730166783515045182532375 17554148321139982097229836138647
    [1316182590973198582184653606272] = true := by
  decide +kernel

end LnFloorCert
