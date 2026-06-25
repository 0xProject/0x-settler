import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell12 : checkCoverK kB certErrGeLit 77862472582514100371703091045 77949071289735361475558199408
    [86598707221261103855108363] = true := by
  decide +kernel

end LnFloorCert
