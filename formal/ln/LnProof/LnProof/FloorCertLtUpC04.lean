import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell04 : checkCoverK kB certLtUpLit 40233125195560580626250736678 40277017559452910144135999239
    [43892363892329517885262561] = true := by
  decide +kernel

end LnFloorCert
