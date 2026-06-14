import LnProof.FloorCertLit
import LnProof.KroneckerShift

namespace LnFloorCert
open LnPoly

set_option maxRecDepth 100000

theorem geUp_cell06 : checkCoverK kB certGeUpLit 19421947935531588116958905399466 19575368566221044162595721694279
    [153420630689456045636816294813] = true := by
  decide +kernel

end LnFloorCert
