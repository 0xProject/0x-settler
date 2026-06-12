import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell07 : checkCoverK 38000 certGeUpLit 18353121939145251819195376186282 19234718785225251819195376186282
    [881596846080000000000000000000] = true := by
  decide +kernel

end LnFloorCert
