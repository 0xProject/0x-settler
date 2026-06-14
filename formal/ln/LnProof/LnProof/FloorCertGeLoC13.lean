import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell13 : checkCoverK kB certGeLoLit 19970633901034205674142871278321 20282409603651670423947251286015
    [311775702617464749804380007694] = true := by
  decide +kernel

end LnFloorCert
