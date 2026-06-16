import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell14 : checkCoverK kB certLtUpLit 49670427525155949284453311470 56022770974786139918731938181
    [6352343449630190634278626711] = true := by
  decide +kernel

end LnFloorCert
