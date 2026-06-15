import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell14 : checkCoverK kB certLtLoLit 52718533799132937478227897812 56022770974786139918731938181
    [3304237175653202440504040369] = true := by
  decide +kernel

end LnFloorCert
