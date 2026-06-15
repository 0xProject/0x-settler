import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell01 : checkCoverK kB certGeUpLit 59279354618003439001815363431 60868942551995640788375953628
    [1589587933992201786560590197] = true := by
  decide +kernel

end LnFloorCert
