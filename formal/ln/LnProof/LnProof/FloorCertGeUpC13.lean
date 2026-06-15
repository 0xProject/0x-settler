import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell13 : checkCoverK kB certGeUpLit 78899412729359578693986807701 78975185726839709896027368896
    [75772997480131202040561195] = true := by
  decide +kernel

end LnFloorCert
