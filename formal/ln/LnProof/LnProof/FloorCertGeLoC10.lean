import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell10 : checkCoverK kB certGeLoLit 77437517811705333581000648121 77857333859755213679737086192
    [416308118180460844476902507, 3507929869419254259535563] = true := by
  decide +kernel

end LnFloorCert
