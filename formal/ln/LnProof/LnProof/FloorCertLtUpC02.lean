import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell02 : checkCoverK kB certLtUpLit 40149298654143480131116927798 40201343509165054248704163767
    [52044855021574117587235969] = true := by
  decide +kernel

end LnFloorCert
