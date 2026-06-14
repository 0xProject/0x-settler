import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell09 : checkCoverK kB certLtUpLit 10828761738119364680208728770970 11461059227350261950503342074044
    [632297489230897270294613303074] = true := by
  decide +kernel

end LnFloorCert
