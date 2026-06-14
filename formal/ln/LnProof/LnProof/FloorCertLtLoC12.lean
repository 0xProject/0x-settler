import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell12 : checkCoverK kB certLtLoLit 13764455152493014279112910224239 14341829369545251819195376186183
    [577374217052237540082465961944] = true := by
  decide +kernel

end LnFloorCert
