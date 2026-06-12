import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell09 : checkCoverK 38000 certGeUpLit 19470449219371196005264548083723 19682606610102545772726802791418
    [212157390731349767462254707695] = true := by
  decide +kernel

end LnFloorCert
