import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell04 : checkCoverK kB certErrLtLit 39763891854368929726387401071 39774662295602570286662651220
    [10770441233640560275250149] = true := by
  decide +kernel

end LnFloorCert
