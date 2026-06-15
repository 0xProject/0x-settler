import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell02 : checkCoverK kB certLtUpLit 40150853919271982033591711250 40205001758610997159114444920
    [54147839339015125522733670] = true := by
  decide +kernel

end LnFloorCert
