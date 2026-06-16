import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell12 : checkCoverK kB certGeUpLit 78838265257980444338216869246 78899360831234549898244564055
    [61095573254105560027694809] = true := by
  decide +kernel

end LnFloorCert
