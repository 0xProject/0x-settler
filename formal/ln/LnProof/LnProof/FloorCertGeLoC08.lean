import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell08 : checkCoverK kB certGeLoLit 74347248156118664616646853614 74496930791525907093206183840
    [149682635407242476559330226] = true := by
  decide +kernel

end LnFloorCert
