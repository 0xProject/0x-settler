import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell15 : checkCoverK kB certLtUpLit 49644314882674105514797500244 50222365124295153396878600218
    [578050241621047882081099974] = true := by
  decide +kernel

end LnFloorCert
