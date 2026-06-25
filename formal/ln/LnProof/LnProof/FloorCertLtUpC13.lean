import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell13 : checkCoverK kB certLtUpLit 45304867147592323391712272579 49088688274983454610883926975
    [3783821127391131219171654396] = true := by
  decide +kernel

end LnFloorCert
