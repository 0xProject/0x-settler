import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell12 : checkCoverK kB certGeUpLit 78835627367648889913153387939 78893863486352981843045626396
    [58236118704091929892238457] = true := by
  decide +kernel

end LnFloorCert
