import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell10 : checkCoverK kB certLtUpLit 11461059227350261950503342074045 11567222306833343375585957498287
    [106163079483081425082615424242] = true := by
  decide +kernel

end LnFloorCert
