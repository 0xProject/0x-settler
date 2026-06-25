import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell11 : checkCoverK kB certLtUpLit 44752276460150783290898176685 45171106034455008017766705000
    [418829574304224726868528315] = true := by
  decide +kernel

end LnFloorCert
