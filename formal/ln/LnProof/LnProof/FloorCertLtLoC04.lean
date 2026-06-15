import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell04 : checkCoverK kB certLtLoLit 39782264730517710874381827396 40683335622502973975961309909
    [901070891985263101579482513] = true := by
  decide +kernel

end LnFloorCert
