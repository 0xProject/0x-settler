import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell13 : checkCoverK kB certErrGeLit 77949071289735361475558199409 78001244224800080662875464165
    [52172935064719187317264756] = true := by
  decide +kernel

end LnFloorCert
