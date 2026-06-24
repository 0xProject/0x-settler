import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell02 : checkCoverK kB certErrLtLit 39730041034935017909079144468 39750332389280211543769847732
    [20291354345193634690703264] = true := by
  decide +kernel

end LnFloorCert
