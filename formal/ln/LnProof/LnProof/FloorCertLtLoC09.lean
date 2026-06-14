import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell09 : checkCoverK kB certLtLoLit 11984914669923891730780665874659 12167033336528931136866442932388
    [182118666605039406085777057729] = true := by
  decide +kernel

end LnFloorCert
