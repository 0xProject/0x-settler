import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell06 : checkCoverK kB certErrLtLit 40928811641811556050178946650 41007581422239460128760466626
    [78769780427904078581519976] = true := by
  decide +kernel

end LnFloorCert
