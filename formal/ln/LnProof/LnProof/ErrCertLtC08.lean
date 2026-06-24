import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell08 : checkCoverK kB certErrLtLit 39776734234069348046975027353 40679522109640282356488826987
    [902787875570934309513799634] = true := by
  decide +kernel

end LnFloorCert
