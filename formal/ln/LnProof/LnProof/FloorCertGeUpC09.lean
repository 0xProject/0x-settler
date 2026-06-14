import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell09 : checkCoverK kB certGeUpLit 19552815870232801636532491927589 19595373564433855905048532370544
    [42557694201054268516040442955] = true := by
  decide +kernel

end LnFloorCert
