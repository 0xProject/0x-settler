import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell07 : checkCoverK kB certLtUpLit 42015714968624513035526540309 42105566798542397566218396417
    [79769949497470434979694626, 10081880420414095712161481] = true := by
  decide +kernel

end LnFloorCert
