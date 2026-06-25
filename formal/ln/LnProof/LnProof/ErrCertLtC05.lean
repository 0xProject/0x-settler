import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell05 : checkCoverK kB certErrLtLit 39774662295602570286662651221 40679997165554683551591585807
    [905334869952113264928934586] = true := by
  decide +kernel

end LnFloorCert
