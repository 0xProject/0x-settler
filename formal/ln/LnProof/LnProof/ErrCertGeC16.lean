import LnProof.ErrCertGeLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem errGe_cell16 : checkCoverK kB certErrGeLit 78082016047349163698545554609 79228162514264337593543950335
    [1146146466915173894998395726] = true := by
  decide +kernel

end LnFloorCert
