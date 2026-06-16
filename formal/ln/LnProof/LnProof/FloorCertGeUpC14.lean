import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell14 : checkCoverK kB certGeUpLit 78974765181663678167544320607 79228162514264337593543950335
    [253397332600659425999629728] = true := by
  decide +kernel

end LnFloorCert
