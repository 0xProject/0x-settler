import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell01 : checkCoverK kB certGeLoLit 62248863508307989581262617184 63042232383408656869457414737
    [793368875100667288194797553] = true := by
  decide +kernel

end LnFloorCert
