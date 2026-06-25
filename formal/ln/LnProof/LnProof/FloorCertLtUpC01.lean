import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell01 : checkCoverK kB certLtUpLit 39982094489912265292386939331 40149298654143480131116927797
    [167204164231214838729988466] = true := by
  decide +kernel

end LnFloorCert
