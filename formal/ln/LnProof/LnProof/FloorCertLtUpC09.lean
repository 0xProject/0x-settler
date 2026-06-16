import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell09 : checkCoverK kB certLtUpLit 42244228633829548558923780244 44761589464445247665450168506
    [2517360830615699106526388262] = true := by
  decide +kernel

end LnFloorCert
