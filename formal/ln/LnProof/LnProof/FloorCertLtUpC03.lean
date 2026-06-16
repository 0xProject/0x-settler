import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell03 : checkCoverK kB certLtUpLit 40205001758610997159114444921 40233125195560580626250736677
    [28123436949583467136291756] = true := by
  decide +kernel

end LnFloorCert
