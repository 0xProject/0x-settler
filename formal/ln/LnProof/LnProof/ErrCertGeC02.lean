import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell02 : checkCoverK kB certErrGeLit 62976353586526539109099492226 63240749540139122990169033120
    [264395953612583881069540894] = true := by
  decide +kernel

end LnFloorCert
