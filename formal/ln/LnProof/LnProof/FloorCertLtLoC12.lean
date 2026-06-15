import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell12 : checkCoverK kB certLtLoLit 47296288103334780980946196295 51908288197118955507511003853
    [4612000093784174526564807558] = true := by
  decide +kernel

end LnFloorCert
