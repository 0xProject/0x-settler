import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell07 : checkCoverK kB certGeLoLit 19827011133089491901331066646784 19943464632857537495188824650085
    [116453499768045593857758003301] = true := by
  decide +kernel

end LnFloorCert
