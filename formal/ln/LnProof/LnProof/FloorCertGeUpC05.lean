import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell05 : checkCoverK kB certGeUpLit 18486789396570097711302005717407 19421947935531588116958905399465
    [935158538961490405656899682058] = true := by
  decide +kernel

end LnFloorCert
