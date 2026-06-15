import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell02 : checkCoverK kB certLtUpLit 40150840529484459081173267989 40204970326660617590528065820
    [54129797176158509354797831] = true := by
  decide +kernel

end LnFloorCert
