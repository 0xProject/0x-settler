import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell10 : checkCoverK kB certLtUpLit 44761589464445247665450168507 45182237044145709221717782607
    [411722407398744470380041699, 8925172301717085887572400] = true := by
  decide +kernel

end LnFloorCert
