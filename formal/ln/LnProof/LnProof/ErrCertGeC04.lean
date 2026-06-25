import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell04 : checkCoverK kB certErrGeLit 68520601063356091078894418603 69177516330888078974756550732
    [656915267531987895862132129] = true := by
  decide +kernel

end LnFloorCert
