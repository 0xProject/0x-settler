import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell16 : checkCoverK kB certLtUpLit 50222365124295153396878600219 56022770974786139918731938181
    [5800405850490986521853337962] = true := by
  decide +kernel

end LnFloorCert
