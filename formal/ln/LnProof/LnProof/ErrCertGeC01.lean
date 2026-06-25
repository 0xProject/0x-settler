import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell01 : checkCoverK kB certErrGeLit 62240135811560208137865971483 63000796656518944161749483048
    [760660844958736023883511565] = true := by
  decide +kernel

end LnFloorCert
