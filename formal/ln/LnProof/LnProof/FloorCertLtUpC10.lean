import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell10 : checkCoverK kB certLtUpLit 12790326440757707523851639277547 14341829369545251819195376186183
    [1551502928787544295343736908636] = true := by
  decide +kernel

end LnFloorCert
