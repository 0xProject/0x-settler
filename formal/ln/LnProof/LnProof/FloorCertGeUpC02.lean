import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell02 : checkCoverK kB certGeUpLit 60868875837913635876431211873 65647199166770921808412026255
    [4778323328857285931980814382] = true := by
  decide +kernel

end LnFloorCert
