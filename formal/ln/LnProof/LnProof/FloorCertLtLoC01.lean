import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell01 : checkCoverK kB certLtLoLit 39691571409046729502659323846 39733107469079426087592196000
    [41536060032696584932872154] = true := by
  decide +kernel

end LnFloorCert
