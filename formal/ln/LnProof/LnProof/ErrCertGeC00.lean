import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell00 : checkCoverK kB certErrGeLit 56022770974786139918731938273 62240135811560208137865971482
    [6217364836774068219134033209] = true := by
  decide +kernel

end LnFloorCert
