import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell11 : checkCoverK kB certErrLtLit 43447171544436788464147782268 43575643795639300685954607736
    [128472251202512221806825468] = true := by
  decide +kernel

end LnFloorCert
