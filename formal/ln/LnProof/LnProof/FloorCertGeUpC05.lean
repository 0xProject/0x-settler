import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell05 : checkCoverK kB certGeUpLit 71273341474262273478494121529 71949306592399438020188468464
    [675965118137164541694346935] = true := by
  decide +kernel

end LnFloorCert
