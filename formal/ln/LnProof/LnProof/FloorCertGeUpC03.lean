import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell03 : checkCoverK kB certGeUpLit 65647199166770921808412026256 66326012476199512076492819330
    [678813309428590268080793074] = true := by
  decide +kernel

end LnFloorCert
