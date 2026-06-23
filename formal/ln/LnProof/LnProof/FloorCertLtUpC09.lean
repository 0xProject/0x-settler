import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell09 : checkCoverK kB certLtUpLit 42244228633829548558923780244 44761589464445247665450168506
    [2515235986461439168093797907, 2124844154259938432590354] = true := by
  decide +kernel

end LnFloorCert
