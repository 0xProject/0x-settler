import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell11 : checkCoverK kB certLtUpLit 45182202408663635743116208965 45358307431374604781736520061
    [176105022710969038620311096] = true := by
  decide +kernel

end LnFloorCert
