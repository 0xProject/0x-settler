import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell21 : checkCoverK kB certErrLtLit 52718050121226925508670314995 56022770974786139918731938181
    [3304720853559214410061623186] = true := by
  decide +kernel

end LnFloorCert
