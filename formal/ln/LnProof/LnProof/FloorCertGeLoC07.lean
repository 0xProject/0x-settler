import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell07 : checkCoverK kB certGeLoLit 73761687789119228727691347874 74347359659513480232328600324
    [576326282334894360390784099, 9345588059357144246468350] = true := by
  decide +kernel

end LnFloorCert
