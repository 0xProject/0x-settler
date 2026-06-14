import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell02 : checkCoverK kB certLtUpLit 10278716364765519398518749303921 10292712939884798707436596404544
    [13996575119279308917847100623] = true := by
  decide +kernel

end LnFloorCert
