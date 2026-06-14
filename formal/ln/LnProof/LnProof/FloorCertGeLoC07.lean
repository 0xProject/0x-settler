import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell07 : checkCoverK kB certGeLoLit 18731392659145251819195376186282 18951791870665251819195376186282
    [220399211520000000000000000000] = true := by
  decide +kernel

end LnFloorCert
