import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell11 : checkCoverK kB certGeLoLit 77857333859755213679737086193 77947664376793543259244624794
    [82562763745553785729181410, 7767753292775793778357190] = true := by
  decide +kernel

end LnFloorCert
