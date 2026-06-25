import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell03 : checkCoverK kB certErrGeLit 63425726531882452517671634538 68520601063356091078894418602
    [5094874531473638561222784064] = true := by
  decide +kernel

end LnFloorCert
