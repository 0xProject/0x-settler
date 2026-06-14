import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell10 : checkCoverK kB certGeUpLit 19595373564433855905048532370545 20121423903139064408900599034957
    [526050338705208503852066664412] = true := by
  decide +kernel

end LnFloorCert
