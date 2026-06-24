import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell07 : checkCoverK kB certErrLtLit 41007581422239460128760466627 41135431140835574713035759925
    [127849718596114584275293298] = true := by
  decide +kernel

end LnFloorCert
