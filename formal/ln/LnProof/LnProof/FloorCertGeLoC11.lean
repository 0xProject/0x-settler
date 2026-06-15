import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell11 : checkCoverK kB certGeLoLit 77857333859755213679737086193 77947664376793543259244624794
    [90330517038329579507538601] = true := by
  decide +kernel

end LnFloorCert
