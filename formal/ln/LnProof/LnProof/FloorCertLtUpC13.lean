import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell13 : checkCoverK kB certLtUpLit 12570288470101219395936602426122 12716299221720374084609926036921
    [146010751619154688673323610799] = true := by
  decide +kernel

end LnFloorCert
