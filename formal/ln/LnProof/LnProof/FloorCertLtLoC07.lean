import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell07 : checkCoverK kB certLtLoLit 10500929675376587685486809613148 10804067352168065028243107714128
    [303137676791477342756298100980] = true := by
  decide +kernel

end LnFloorCert
