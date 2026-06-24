import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell15 : checkCoverK kB certErrLtLit 52819343388154448027094034824 56022770974786139918731938181
    [3203427586631691891637903357] = true := by
  decide +kernel

end LnFloorCert
