import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell00 : checkCoverK kB certGeLoLit 14341829369545251819195376186275 15948890630125408368526546481898
    [1607061260580156549331170295623] = true := by
  decide +kernel

end LnFloorCert
