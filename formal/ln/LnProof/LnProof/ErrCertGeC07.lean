import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell07 : checkCoverK kB certErrGeLit 73730515843223541190152991238 74334604836325087960096058977
    [604088993101546769943067739] = true := by
  decide +kernel

end LnFloorCert
