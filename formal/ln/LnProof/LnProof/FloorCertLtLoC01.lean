import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell01 : checkCoverK kB certLtLoLit 39691568842842447562319269666 39733100139740266608218414413
    [41000183263333662637606721, 531113634485383261538025] = true := by
  decide +kernel

end LnFloorCert
