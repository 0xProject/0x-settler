import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell00 : checkCoverK kB certGeUpLit 56022770974786139918731938273 59266081817351235913474286845
    [3243310842565095994742348572] = true := by
  decide +kernel

end LnFloorCert
