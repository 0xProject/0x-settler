import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell13 : checkCoverK kB certGeLoLit 78001071025949577278638182917 79228162514264337593543950335
    [1227091488314760314905767418] = true := by
  decide +kernel

end LnFloorCert
