import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell10 : checkCoverK kB certGeUpLit 20217582813988731407505919116502 20282409603651670423947251286015
    [64826789662939016441332169513] = true := by
  decide +kernel

end LnFloorCert
