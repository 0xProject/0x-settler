import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell08 : checkCoverK kB certGeUpLit 19420493055983681582258478985971 19552815870232801636532491927588
    [132322814249120054274012941617] = true := by
  decide +kernel

end LnFloorCert
