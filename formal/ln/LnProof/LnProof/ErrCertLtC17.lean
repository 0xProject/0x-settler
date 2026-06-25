import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell17 : checkCoverK kB certErrLtLit 53036600108885143092541888945 56022770974786139918731938181
    [2986170865900996826190049236] = true := by
  decide +kernel

end LnFloorCert
