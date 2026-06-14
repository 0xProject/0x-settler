import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell06 : checkCoverK kB certGeUpLit 18423857642692923866673020234057 18535920551598687926393298794814
    [112062908905764059720278560757] = true := by
  decide +kernel

end LnFloorCert
