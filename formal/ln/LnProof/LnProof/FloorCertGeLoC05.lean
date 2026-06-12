import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell05 : checkCoverK 38000 certGeLoLit 17697421049545251819195376186280 18241616633545251819195376186280
    [544195584000000000000000000000] = true := by
  decide +kernel

end LnFloorCert
