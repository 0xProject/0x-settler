import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltUp_cell07 : checkCoverK kB certLtUpLit 42015714968624513035526540309 42105566798542397566218396417
    [89851829917884530691856108] = true := by
  decide +kernel

end LnFloorCert
