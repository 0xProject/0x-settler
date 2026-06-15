import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell08 : checkCoverK kB certLtUpLit 42105566798542397566218396418 42244228633829548558923780243
    [138661835287150992705383825] = true := by
  decide +kernel

end LnFloorCert
