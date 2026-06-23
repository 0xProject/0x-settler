import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell03 : checkCoverK kB certGeUpLit 65647199166770921808412026256 66326012476199512076492819330
    [654510403699197420623647603, 24302905729392847457145470] = true := by
  decide +kernel

end LnFloorCert
