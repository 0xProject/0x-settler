import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell06 : checkCoverK kB certLtUpLit 10914799648682411772312803110963 11484527015770799509484495012553
    [569727367088387737171691901590] = true := by
  decide +kernel

end LnFloorCert
