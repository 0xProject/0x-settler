import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell03 : checkCoverK kB certLtLoLit 10185047743608951581783796515313 10417293044196343000101522094334
    [232245300587391418317725579021] = true := by
  decide +kernel

end LnFloorCert
