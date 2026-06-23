import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell10 : checkCoverK kB certErrGeLit 74523753466302552435307247887 77442057038427372518395562865
    [2918303572124820083088314978] = true := by
  decide +kernel

end LnFloorCert
