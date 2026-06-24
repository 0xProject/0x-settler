import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell18 : checkCoverK kB certErrLtLit 47265409858234429269501593573 47863312455617981068416176220
    [597902597383551798914582647] = true := by
  decide +kernel

end LnFloorCert
