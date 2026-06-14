import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell03 : checkCoverK kB certGeUpLit 16805676617545692639475832291231 16979427757686177564090726988484
    [173751140140484924614894697253] = true := by
  decide +kernel

end LnFloorCert
