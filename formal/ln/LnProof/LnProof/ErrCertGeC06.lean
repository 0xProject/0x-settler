import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell06 : checkCoverK kB certErrGeLit 69402331473388570025030861839 73730515843223541190152991237
    [4328184369834971165122129398] = true := by
  decide +kernel

end LnFloorCert
