import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell05 : checkCoverK kB certErrGeLit 69177516330888078974756550733 69402331473388570025030861838
    [224815142500491050274311105] = true := by
  decide +kernel

end LnFloorCert
