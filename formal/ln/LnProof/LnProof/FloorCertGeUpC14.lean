import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell14 : checkCoverK kB certGeUpLit 78941888558111820679980811877 79228162514264337593543950335
    [286273956152516913563138458] = true := by
  decide +kernel

end LnFloorCert
