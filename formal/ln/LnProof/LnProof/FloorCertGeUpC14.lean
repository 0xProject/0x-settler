import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell14 : checkCoverK kB certGeUpLit 78975185726839709896027368897 79228162514264337593543950335
    [252976787424627697516581438] = true := by
  decide +kernel

end LnFloorCert
