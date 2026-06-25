import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell14 : checkCoverK kB certLtUpLit 49088688274983454610883926976 49644314882674105514797500243
    [555626607690650903913573267] = true := by
  decide +kernel

end LnFloorCert
