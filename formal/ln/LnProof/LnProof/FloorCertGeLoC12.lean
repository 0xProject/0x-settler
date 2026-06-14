import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell12 : checkCoverK kB certGeLoLit 19955291445289458852554233347636 19970633901034205674142871278320
    [15342455744746821588637930684] = true := by
  decide +kernel

end LnFloorCert
