import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell01 : checkCoverK kB certLtUpLit 10236733219469637195766410765228 10283083180369672200219960462811
    [46349960900035004453549697583] = true := by
  decide +kernel

end LnFloorCert
