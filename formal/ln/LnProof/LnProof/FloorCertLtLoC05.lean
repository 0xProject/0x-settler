import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell05 : checkCoverK kB certLtLoLit 10414913185454529924459501364971 10478857288205549822693249459120
    [63944102751019898233748094149] = true := by
  decide +kernel

end LnFloorCert
