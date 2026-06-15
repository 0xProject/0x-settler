import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell03 : checkCoverK kB certLtLoLit 39757671805730023558503456122 39782264730517710874381827395
    [24592924787687315878371273] = true := by
  decide +kernel

end LnFloorCert
