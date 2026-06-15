import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell01 : checkCoverK kB certLtUpLit 39982530726060180992616285303 40150840529484459081173267988
    [168309803424278088556982685] = true := by
  decide +kernel

end LnFloorCert
