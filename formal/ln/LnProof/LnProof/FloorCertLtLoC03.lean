import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell03 : checkCoverK kB certLtLoLit 39757653172445695310837028836 39782184972069981508068781991
    [24531799624286197231753155] = true := by
  decide +kernel

end LnFloorCert
