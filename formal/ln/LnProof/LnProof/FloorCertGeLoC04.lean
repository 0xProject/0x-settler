import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell04 : checkCoverK kB certGeLoLit 17395090169545251819195376186279 17697421049545251819195376186279
    [302330880000000000000000000000] = true := by
  decide +kernel

end LnFloorCert
