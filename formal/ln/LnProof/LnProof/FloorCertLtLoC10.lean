import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem ltLo_cell10 : checkCoverK kB certLtLoLit 43555340935173254406944988026 46779569004398866896767989130
    [3224228069225612489823001104] = true := by
  decide +kernel

end LnFloorCert
