import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell12 : checkCoverK kB certLtUpLit 45358307431374604781736520062 49100597176785563576919508299
    [3742289745410958795182988237] = true := by
  decide +kernel

end LnFloorCert
