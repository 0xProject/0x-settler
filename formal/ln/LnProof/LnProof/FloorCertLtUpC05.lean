import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell05 : checkCoverK kB certLtUpLit 40277017559452910144135999240 41692588105644715585450931157
    [1414487731308392122175487989, 1082814883413319139443927] = true := by
  decide +kernel

end LnFloorCert
