import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell02 : checkCoverK kB certGeLoLit 63042232383408656869457414738 64929052012891719377728977367
    [1064949080910029635326401594, 821870548573032872945161034] = true := by
  decide +kernel

end LnFloorCert
