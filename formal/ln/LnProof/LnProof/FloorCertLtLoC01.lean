import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell01 : checkCoverK kB certLtLoLit 39691568842842447562319269666 39733100139740266608218414413
    [41531296897819045899144747] = true := by
  decide +kernel

end LnFloorCert
