import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell05 : checkCoverK kB certLtUpLit 10770151616997275407327261993132 10914799648682411772312803110962
    [144648031685136364985541117830] = true := by
  decide +kernel

end LnFloorCert
