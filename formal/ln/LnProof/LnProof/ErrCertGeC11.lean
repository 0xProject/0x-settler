import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell11 : checkCoverK kB certErrGeLit 77442057038427372518395562866 77852846065527338130569252120
    [410789027099965612173689254] = true := by
  decide +kernel

end LnFloorCert
