import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell06 : checkCoverK kB certErrLtLit 39768794545599430872698185559 39770663872413954292287692847
    [1869326814523419589507288] = true := by
  decide +kernel

end LnFloorCert
