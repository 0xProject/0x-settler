import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell12 : checkCoverK 38000 certGeUpLit 20162553774023688135563636774606 20216488897356280165336263304739
    [53935123332592029772626530133] = true := by
  decide +kernel

end LnFloorCert
