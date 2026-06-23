import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell11 : checkCoverK kB certGeUpLit 78599445424075384278202074397 78838265257980444338216869245
    [237144326000088706715353700, 1675507904971353299441147] = true := by
  decide +kernel

end LnFloorCert
