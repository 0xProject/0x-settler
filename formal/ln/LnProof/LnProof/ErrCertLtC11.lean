import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell11 : checkCoverK kB certErrLtLit 40987649777297210133226675107 41021199587189415288102588115
    [33549809892205154875913008] = true := by
  decide +kernel

end LnFloorCert
