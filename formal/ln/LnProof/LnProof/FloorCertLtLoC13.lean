import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell13 : checkCoverK kB certLtLoLit 51908282562281673025522611128 52718525787343046817539678213
    [771592286713047586577844713, 38650938348326205439222371] = true := by
  decide +kernel

end LnFloorCert
