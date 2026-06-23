import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell01 : checkCoverK kB certErrGeLit 62235000306952571703781716894 62976353586526539109099492225
    [741353279573967405317775331] = true := by
  decide +kernel

end LnFloorCert
