import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell10 : checkCoverK kB certErrGeLit 74922450207405969458838387099 77498269107963454383074120902
    [2575818900557484924235733803] = true := by
  decide +kernel

end LnFloorCert
