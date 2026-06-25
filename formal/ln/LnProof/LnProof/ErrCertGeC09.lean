import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell09 : checkCoverK kB certErrGeLit 74478977508043445090363886841 74922450207405969458838387098
    [443472699362524368474500257] = true := by
  decide +kernel

end LnFloorCert
