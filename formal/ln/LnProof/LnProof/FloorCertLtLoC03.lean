import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell03 : checkCoverK kB certLtLoLit 10177940795541626959104557434486 10184160994906416673806253181241
    [6220199364789714701695746755] = true := by
  decide +kernel

end LnFloorCert
