import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell11 : checkCoverK kB certErrGeLit 77498269107963454383074120903 77862472582514100371703091044
    [364203474550645988628970141] = true := by
  decide +kernel

end LnFloorCert
