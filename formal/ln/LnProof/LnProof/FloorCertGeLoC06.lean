import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell06 : checkCoverK kB certGeLoLit 69642734452756761581840935358 73761496465424587311876899021
    [4118762012667825730035963663] = true := by
  decide +kernel

end LnFloorCert
