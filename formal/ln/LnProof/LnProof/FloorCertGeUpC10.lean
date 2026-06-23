import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell10 : checkCoverK kB certGeUpLit 76545349455617885268024766254 78599445424075384278202074396
    [2053394912423315526385683969, 701056034183483791624172] = true := by
  decide +kernel

end LnFloorCert
