import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geLo_cell05 : checkCoverK kB certGeLoLit 69233034096605084266152150504 69642734452756761581840935357
    [409700356151677315688784853] = true := by
  decide +kernel

end LnFloorCert
