import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell10 : checkCoverK kB certGeUpLit 76512522319826533298339061378 78595188666574508701639272524
    [2082666346747975403300211146] = true := by
  decide +kernel

end LnFloorCert
