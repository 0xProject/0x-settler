import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell00 : checkCoverK kB certGeUpLit 56022770974786139918731938273 59279354229259720917350213723
    [3256583254473580998618275450] = true := by
  decide +kernel

end LnFloorCert
