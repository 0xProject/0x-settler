import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell07 : checkCoverK kB certGeUpLit 72409504182901287012502905606 75861812401389825744148636453
    [3452308218488538731645730847] = true := by
  decide +kernel

end LnFloorCert
