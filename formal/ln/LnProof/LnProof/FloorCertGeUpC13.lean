import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell13 : checkCoverK kB certGeUpLit 78899360831234549898244564056 78974765181663678167544320606
    [60129469292558073514408233, 15274881136570195785348316] = true := by
  decide +kernel

end LnFloorCert
