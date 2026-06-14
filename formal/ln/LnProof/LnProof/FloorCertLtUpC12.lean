import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell12 : checkCoverK kB certLtUpLit 11614401749478021771482220450252 12570288470101219395936602426121
    [955886720623197624454381975869] = true := by
  decide +kernel

end LnFloorCert
