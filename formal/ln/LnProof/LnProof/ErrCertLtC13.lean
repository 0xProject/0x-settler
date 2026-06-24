import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell13 : checkCoverK kB certErrLtLit 41120594256801000951027113789 43087646344191582790285854567
    [1967052087390581839258740778] = true := by
  decide +kernel

end LnFloorCert
