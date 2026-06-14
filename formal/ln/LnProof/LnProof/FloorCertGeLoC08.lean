import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell08 : checkCoverK kB certGeLoLit 18951791870665251819195376186283 19348510451401251819195376186283
    [396718580736000000000000000000] = true := by
  decide +kernel

end LnFloorCert
