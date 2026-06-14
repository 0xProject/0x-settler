import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell06 : checkCoverK kB certLtLoLit 10478857288205549822693249459121 10500929675376587685486809613147
    [22072387171037862793560154026] = true := by
  decide +kernel

end LnFloorCert
