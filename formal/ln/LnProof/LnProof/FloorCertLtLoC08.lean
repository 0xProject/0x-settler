import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell08 : checkCoverK kB certLtLoLit 42434861454155548723387563153 43340936784615056347798031794
    [902674723278695753244011343, 3400607180811871166457297] = true := by
  decide +kernel

end LnFloorCert
