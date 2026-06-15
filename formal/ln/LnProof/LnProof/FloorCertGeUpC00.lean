import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell00 : checkCoverK kB certGeUpLit 56022770974786139918731938273 59279354618003439001815363430
    [3256583643217299083083425157] = true := by
  decide +kernel

end LnFloorCert
