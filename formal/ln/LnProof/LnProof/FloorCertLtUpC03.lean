import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell03 : checkCoverK kB certLtUpLit 10292712939884798707436596404545 10300290733559920510761662675178
    [7577793675121803325066270633] = true := by
  decide +kernel

end LnFloorCert
