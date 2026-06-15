import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell01 : checkCoverK kB certGeUpLit 59279354229259720917350213724 60868875837913635876431211872
    [1589521608653914959080998148] = true := by
  decide +kernel

end LnFloorCert
