import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell02 : checkCoverK kB certLtLoLit 39733100139740266608218414414 39757653172445695310837028835
    [23319567683643544854454624, 1233465021785157764159796] = true := by
  decide +kernel

end LnFloorCert
