import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell14 : checkCoverK kB certErrGeLit 77969489922568434205266494790 77989822678558353447718470814
    [20332755989919242451976024] = true := by
  decide +kernel

end LnFloorCert
