import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell03 : checkCoverK kB certLtUpLit 40205001758610997159114444921 40233125195560580626250736677
    [22293268174262348046297022, 5830168775321119089994733] = true := by
  decide +kernel

end LnFloorCert
