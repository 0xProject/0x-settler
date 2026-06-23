import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell15 : checkCoverK kB certErrGeLit 77989822678558353447718470815 78082016047349163698545554608
    [92193368790810250827083793] = true := by
  decide +kernel

end LnFloorCert
