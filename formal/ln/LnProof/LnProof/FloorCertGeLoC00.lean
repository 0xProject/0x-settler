import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell00 : checkCoverK kB certGeLoLit 56022770974786139918731938273 62248863508307989581262617183
    [6226092533521849662530678910] = true := by
  decide +kernel

end LnFloorCert
