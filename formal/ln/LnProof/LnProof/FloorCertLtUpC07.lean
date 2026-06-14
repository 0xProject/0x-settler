import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell07 : checkCoverK kB certLtUpLit 10756618135670645788065926471905 10779963205013996747845870058712
    [23345069343350959779943586807] = true := by
  decide +kernel

end LnFloorCert
