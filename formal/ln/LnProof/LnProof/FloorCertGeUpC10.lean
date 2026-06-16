import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell10 : checkCoverK kB certGeUpLit 76545349455617885268024766254 78599445424075384278202074396
    [2054095968457499010177308142] = true := by
  decide +kernel

end LnFloorCert
