import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell06 : checkCoverK kB certLtUpLit 10675431702120254763124784810887 10756618135670645788065926471904
    [81186433550391024941141661017] = true := by
  decide +kernel

end LnFloorCert
