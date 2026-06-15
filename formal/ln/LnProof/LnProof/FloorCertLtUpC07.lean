import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell07 : checkCoverK kB certLtUpLit 42015659986837763307254425670 42105474339119878441107071643
    [89814352282115133852645973] = true := by
  decide +kernel

end LnFloorCert
