import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell08 : checkCoverK kB certErrGeLit 74321545568138162293005832387 74445984601364202409568704861
    [124439033226040116562872474] = true := by
  decide +kernel

end LnFloorCert
