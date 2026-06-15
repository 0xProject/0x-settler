import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell03 : checkCoverK kB certLtUpLit 40204970326660617590528065821 40233044689780073357909666320
    [28074363119455767381600499] = true := by
  decide +kernel

end LnFloorCert
