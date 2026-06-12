import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell09 : checkCoverK 38000 certLtUpLit 12348468016417835211973625643017 12705514739080235211973625643017
    [357046722662400000000000000000] = true := by
  decide +kernel

end LnFloorCert
