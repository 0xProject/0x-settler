import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell02 : checkCoverK kB certErrGeLit 63000796656518944161749483049 63425726531882452517671634537
    [424929875363508355922151488] = true := by
  decide +kernel

end LnFloorCert
