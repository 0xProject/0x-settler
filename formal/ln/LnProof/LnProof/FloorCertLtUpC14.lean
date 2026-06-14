import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell14 : checkCoverK kB certLtUpLit 12716299221720374084609926036922 14341829369545251819195376186183
    [1625530147824877734585450149261] = true := by
  decide +kernel

end LnFloorCert
