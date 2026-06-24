import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell05 : checkCoverK kB certErrLtLit 40680904853992493020014255643 40928811641811556050178946649
    [247906787819063030164691006] = true := by
  decide +kernel

end LnFloorCert
