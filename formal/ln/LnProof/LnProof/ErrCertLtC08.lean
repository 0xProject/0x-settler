import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell08 : checkCoverK kB certErrLtLit 41135431140835574713035759926 43095658317834209710916769050
    [1960227176998634997881009124] = true := by
  decide +kernel

end LnFloorCert
