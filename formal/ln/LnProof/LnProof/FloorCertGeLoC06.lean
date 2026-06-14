import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell06 : checkCoverK kB certGeLoLit 17852105151840201335476027974487 18888004859357826028947861809707
    [1035899707517624693471833835220] = true := by
  decide +kernel

end LnFloorCert
