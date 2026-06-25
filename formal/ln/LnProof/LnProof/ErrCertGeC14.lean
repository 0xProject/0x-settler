import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell14 : checkCoverK kB certErrGeLit 78001244224800080662875464166 79228162514264337593543950335
    [1226918289464256930668486169] = true := by
  decide +kernel

end LnFloorCert
