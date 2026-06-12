import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell12 : checkCoverK 38000 certLtLoLit 13463356876825643211973625643020 14341829369545251819195376186183
    [878472492719608607221750543163] = true := by
  decide +kernel

end LnFloorCert
