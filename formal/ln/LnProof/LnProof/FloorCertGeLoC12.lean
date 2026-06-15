import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell12 : checkCoverK kB certGeLoLit 77947664376793543259244624795 78001071025949577278638182916
    [53406649156034019393558121] = true := by
  decide +kernel

end LnFloorCert
