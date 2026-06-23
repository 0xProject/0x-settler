import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell13 : checkCoverK kB certErrGeLit 77935952197004339716648454442 77969489922568434205266494789
    [33537725564094488618040347] = true := by
  decide +kernel

end LnFloorCert
