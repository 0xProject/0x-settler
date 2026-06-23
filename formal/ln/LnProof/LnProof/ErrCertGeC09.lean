import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell09 : checkCoverK kB certErrGeLit 74445984601364202409568704862 74523753466302552435307247886
    [77768864938350025738543024] = true := by
  decide +kernel

end LnFloorCert
