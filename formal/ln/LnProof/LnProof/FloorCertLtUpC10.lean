import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell10 : checkCoverK kB certLtUpLit 44761589464445247665450168507 45182237044145709221717782607
    [420647579700461556267614100] = true := by
  decide +kernel

end LnFloorCert
