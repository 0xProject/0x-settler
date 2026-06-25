import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell03 : checkCoverK kB certLtUpLit 40201343509165054248704163768 40224348129155411324248597878
    [23004619990357075544434110] = true := by
  decide +kernel

end LnFloorCert
