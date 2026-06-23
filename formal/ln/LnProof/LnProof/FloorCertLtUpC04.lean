import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell04 : checkCoverK kB certLtUpLit 40233125195560580626250736678 40277017559452910144135999239
    [17846004908524483842207852, 26046358983805034043054708] = true := by
  decide +kernel

end LnFloorCert
