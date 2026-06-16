import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell11 : checkCoverK kB certLtUpLit 45182237044145709221717782608 45358461709730537512255462320
    [176224665584828290537679712] = true := by
  decide +kernel

end LnFloorCert
