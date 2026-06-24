import LnProof.ErrCertLtLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errLt_cell16 : checkCoverK kB certErrLtLit 43550321627651620471295348780 46772661970268323857756182433
    [3222340342616703386460833653] = true := by
  decide +kernel

end LnFloorCert
