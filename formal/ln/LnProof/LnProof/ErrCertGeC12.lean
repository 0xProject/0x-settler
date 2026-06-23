import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell12 : checkCoverK kB certErrGeLit 77852846065527338130569252121 77935952197004339716648454441
    [83106131477001586079202320] = true := by
  decide +kernel

end LnFloorCert
