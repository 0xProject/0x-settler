import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell02 : checkCoverK kB certLtLoLit 39733107469079426087592196001 39757671805730023558503456121
    [24564336650597470911260120] = true := by
  decide +kernel

end LnFloorCert
