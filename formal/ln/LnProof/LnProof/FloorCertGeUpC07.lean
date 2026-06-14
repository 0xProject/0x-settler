import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell07 : checkCoverK kB certGeUpLit 18535920551598687926393298794815 19420493055983681582258478985970
    [884572504384993655865180191155] = true := by
  decide +kernel

end LnFloorCert
