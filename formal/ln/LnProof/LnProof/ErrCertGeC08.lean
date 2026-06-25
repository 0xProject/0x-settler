import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell08 : checkCoverK kB certErrGeLit 74334604836325087960096058978 74478977508043445090363886840
    [144372671718357130267827862] = true := by
  decide +kernel

end LnFloorCert
