import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell02 : checkCoverK kB certGeLoLit 63042232383408656869457414738 64929052012891719377728977367
    [1886819629483062508271562629] = true := by
  decide +kernel

end LnFloorCert
