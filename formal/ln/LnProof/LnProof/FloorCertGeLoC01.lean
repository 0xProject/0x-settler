import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell01 : checkCoverK kB certGeLoLit 62248863508307989581262617184 63042232383408656869457414737
    [773152159907500154491704824, 20216715193167133703092728] = true := by
  decide +kernel

end LnFloorCert
