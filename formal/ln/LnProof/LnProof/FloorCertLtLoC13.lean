import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell13 : checkCoverK kB certLtLoLit 51908288197118955507511003854 52718533799132937478227897811
    [810245602013981970716893957] = true := by
  decide +kernel

end LnFloorCert
