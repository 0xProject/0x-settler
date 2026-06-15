import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell06 : checkCoverK kB certLtUpLit 41692401823923536401685262438 42015659986837763307254425669
    [323258162914226905569163231] = true := by
  decide +kernel

end LnFloorCert
