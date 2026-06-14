import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell07 : checkCoverK kB certGeLoLit 18888004859357826028947861809708 19034951989452419220406092183059
    [146947130094593191458230373351] = true := by
  decide +kernel

end LnFloorCert
