import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell05 : checkCoverK kB certErrLtLit 39765961139795848653992550333 39768794545599430872698185558
    [2833405803582218705635225] = true := by
  decide +kernel

end LnFloorCert
