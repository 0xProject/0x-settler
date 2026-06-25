import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell09 : checkCoverK kB certLtUpLit 42091380544708413934368876662 42146662162229712555615056322
    [55281617521298621246179660] = true := by
  decide +kernel

end LnFloorCert
