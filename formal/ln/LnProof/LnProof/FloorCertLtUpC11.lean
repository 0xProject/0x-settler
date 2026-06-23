import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell11 : checkCoverK kB certLtUpLit 45182237044145709221717782608 45358461709730537512255462320
    [140774746367837690550460732, 35449919216990599987218979] = true := by
  decide +kernel

end LnFloorCert
