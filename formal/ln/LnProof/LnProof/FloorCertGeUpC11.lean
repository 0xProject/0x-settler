import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell11 : checkCoverK kB certGeUpLit 20121423903139064408900599034958 20182572396030540906326124652209
    [61148492891476497425525617251] = true := by
  decide +kernel

end LnFloorCert
