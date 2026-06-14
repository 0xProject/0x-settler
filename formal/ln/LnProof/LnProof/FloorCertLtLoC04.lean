import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell04 : checkCoverK kB certLtLoLit 10417293044196343000101522094335 10488077265272720113023495514352
    [70784221076377112921973420017] = true := by
  decide +kernel

end LnFloorCert
