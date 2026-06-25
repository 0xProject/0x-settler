import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell07 : checkCoverK kB certLtUpLit 41686814657515192596739173674 42010208390739198067655462807
    [323393733224005470916289133] = true := by
  decide +kernel

end LnFloorCert
