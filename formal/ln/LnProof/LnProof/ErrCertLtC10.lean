import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell10 : checkCoverK kB certErrLtLit 43074909657573168724990774476 43447171544436788464147782267
    [372261886863619739157007791] = true := by
  decide +kernel

end LnFloorCert
