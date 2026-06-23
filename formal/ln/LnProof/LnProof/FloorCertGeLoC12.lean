import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell12 : checkCoverK kB certGeLoLit 77947664376793543259244624795 78001071025949577278638182916
    [33900297204464383940454862, 19506351951569635453103258] = true := by
  decide +kernel

end LnFloorCert
