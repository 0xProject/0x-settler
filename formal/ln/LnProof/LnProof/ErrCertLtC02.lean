import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell02 : checkCoverK kB certErrLtLit 39731844495833091299568641515 39754544997383943847916639872
    [22700501550852548347998357] = true := by
  decide +kernel

end LnFloorCert
