import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell12 : checkCoverK kB certErrLtLit 41021199587189415288102588116 41120594256801000951027113788
    [99394669611585662924525672] = true := by
  decide +kernel

end LnFloorCert
